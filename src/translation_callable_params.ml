(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Callable-parameter analysis: which function-typed parameters a recursive
    group or a local fixpoint passes on unchanged, lets escape, or feeds a
    closure back through, and so which callables a function's C++ head may
    not generalise to a deduced template parameter.  Read by
    {!Program_facts} before translation and by the function generators. *)

open Base.Common
open Names
open Base.Core_util
open Util
open Translation_state
open Base.Type_util

module IntSet = Escape.IntSet

(* Walk a Core term and collect source-order parameter indices that are NOT
   simply forwarded unchanged at recursive call sites.  [is_self_call depth f]
   returns true when the head [f] of an application is a self-recursive
   reference at the given binder depth.

   After collect_lams, param source index [i] has de Bruijn index
   [n_params - i] at depth 0, shifted by [depth] under binders. *)
let detect_non_forwarded_params_generic ~is_self_call n_params body =
  let non_fwd = Hashtbl.create 4 in
  let is_forwarded depth i arg =
    let expected_db = n_params - i + depth in
    match arg with
    | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = db; _}; _}
    | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = db; _}; _}
    | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = db; _}; _}
    | Core.Expr.Bound_variable {index = db; _} -> db = expected_db
    | _ -> false
  in
  let rec walk depth = function
    | Core.Expr.Apply {callee = f; arguments = args} when is_self_call depth f ->
      List.iteri
        (fun i arg ->
          if i < n_params && not (is_forwarded depth i arg) then
            Hashtbl.replace non_fwd i true )
        args
    | Core.Expr.Apply {callee = f; arguments = args} ->
      walk depth f;
      List.iter (walk depth) args
    | Core.Expr.Lambda {body; _} -> walk (depth + 1) body
    | Core.Expr.Let {value = e1; body = e2; _} ->
      walk depth e1;
      walk (depth + 1) e2
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      walk depth scrut;
      Array.iter
        (fun {Core.Match.Branch.binders = ids; body = body; _} ->
          walk (depth + List.length ids) body )
        branches
    | Core.Expr.Construct {arguments = args; _} -> List.iter (walk depth) args
    | Core.Expr.Tuple args -> List.iter (walk depth) args
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let bodies = Core.Recursion.Group.bodies rec_group in
      let n = Array.length bodies in
      Array.iter (walk (depth + n)) bodies
    | Core.Expr.Coerce {value = e; _}
    | Core.Expr.Boxed_value {value = e; _}
    | Core.Expr.Lambda_group_barrier {value = e; _} ->
      walk depth e
    | Core.Expr.Persistent_array {elements = elts; default = def} ->
      Array.iter (walk depth) elts;
      walk depth def
    | Core.Expr.Bound_variable _
     |Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> ()
  in
  walk 0 body;
  Hashtbl.fold (fun k _ acc -> k :: acc) non_fwd []

(** The source-order indices of the parameters that a closure may hold on
    to: those named under a lambda the body does not apply on the spot, or
    anywhere when [suspended] -- the whole body is a thunk, as a function
    returning a coinductive is.

    A callable parameter that escapes this way is taken as a [crane::fn]
    rather than generalised to [F &&].  A deduced callable is the caller's
    closure type itself, and every closure that captures it copies it and all
    it captured; a [crane::fn] is converted once, at the call, and shared by
    every capture after that. *)
let escaping_params cx ~suspended n_params body =
  let escaping = Hashtbl.create 4 in
  let rec walk under depth e =
    match e with
    | Core.Expr.Bound_variable {index = db; _} ->
      let i = n_params - db + depth in
      if under && db > depth && i >= 0 && i < n_params then
        Hashtbl.replace escaping i ()
    | Core.Expr.Apply {callee = (Core.Expr.Lambda _ as f); arguments = args} ->
      (* Applied where it is written: the binders the arguments fill run
         here, not later.  Any left over make a closure. *)
      let rec spine n depth = function
        | Core.Expr.Lambda {body = b; _} when n > 0 -> spine (n - 1) (depth + 1) b
        | b -> walk under depth b
      in
      spine (List.length args) depth f;
      List.iter (walk under depth) args
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = (_ :: _ :: _ as args)}
      when Translation_monadic.is_sequential_effect cx Core_effects.Bind use ->
      (* A bind outside reified mode is desugared into statements: its
         continuation runs where it is written, so the binders it opens are
         locals, not a closure's. *)
      let rec spine depth = function
        | Core.Expr.Lambda {body = b; _} -> spine (depth + 1) b
        | b -> walk under depth b
      in
      ( match List.rev args with
      | k :: rest ->
        List.iter (walk under depth) rest;
        spine depth k
      | [] -> () )
    | Core.Expr.Apply {callee = (Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group);
                       arguments = args} ->
      let bodies = Core.Recursion.Group.bodies rec_group in
      (* A local fixpoint entered where it is written, as [let fix go ... in
         go l []] is: its recursion runs here, through a lambda captured by
         reference, and nothing outlives the call. *)
      let n = Array.length bodies in
      let rec spine k depth = function
        | Core.Expr.Lambda {body = b; _} when k > 0 -> spine (k - 1) (depth + 1) b
        | b -> walk under depth b
      in
      Array.iter (spine (List.length args) (depth + n)) bodies;
      List.iter (walk under depth) args
    | Core.Expr.Lambda {body = b; _} -> walk true (depth + 1) b
    | Core.Expr.Apply {callee = f; arguments = args} ->
      walk under depth f;
      List.iter (walk under depth) args
    | Core.Expr.Let {value = e1; body = e2; _} ->
      walk under depth e1;
      walk under (depth + 1) e2
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      walk under depth scrut;
      Array.iter
        (fun {Core.Match.Branch.binders = ids; body = b; _} -> walk under (depth + List.length ids) b)
        branches
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.iter (walk under depth) args
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let bodies = Core.Recursion.Group.bodies rec_group in
      (* A local fixpoint is a closure over its free variables. *)
      let n = Array.length bodies in
      Array.iter (walk true (depth + n)) bodies
    | Core.Expr.Coerce {value = e; _}
    | Core.Expr.Boxed_value {value = e; _}
    | Core.Expr.Lambda_group_barrier {value = e; _} ->
      walk under depth e
    | Core.Expr.Persistent_array {elements = elts; default = def} ->
      Array.iter (walk under depth) elts;
      walk under depth def
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
     |Core.Expr.String _ -> ()
  in
  walk suspended 0 body;
  Hashtbl.fold (fun k () acc -> k :: acc) escaping []

(* Detect non-forwarded params in a local fixpoint body.  Self-references
   use Core.Expr.Bound_variable: after collect_lams strips [n_params] lambda params, the fix
   binding for [fix_idx] in [n_fix] mutual funs is at
   db = [n_params + n_fix - fix_idx], shifted by binder depth. *)
let detect_non_forwarded_params_fix n_params n_fix fix_idx body =
  let base_self_db = n_params + n_fix - fix_idx in
  detect_non_forwarded_params_generic
    ~is_self_call:(fun depth f ->
      (* A coercion around the self-reference (extraction inserts one when the
         fixpoint's type was generalised) must not hide the recursive call. *)
      let strip = Core.Expr.strip_crossings in
      match strip f with
      | Core.Expr.Bound_variable {index = db; _} -> db = base_self_db + depth
      | _ -> false )
    n_params body

(** Detect function-typed parameters that are NOT simply forwarded at
   self-recursive call sites.

   Higher-order function parameters are normally emitted as C++ template
   parameters constrained with [is_invocable_v], preserving the exact lambda
   type for inlining.  However, when a recursive call passes a *different*
   expression (not the parameter variable itself) for a function-typed parameter,
   each recursion level creates a new template instantiation with a distinct type,
   leading to infinite recursive template instantiation.

   The fix: detect which parameters are not forwarded unchanged at any recursive
   call site.  Those parameters are emitted as [std::function] instead of template
   parameters, since [std::function] is a concrete type that stays the same
   regardless of wrapping.

   Parameters that ARE forwarded unchanged (e.g., a predicate [p] passed as-is in
   [partition_cps p rest (fun ...)]) keep their template parameter status.
   Non-recursive higher-order functions like [tree_rect] are unaffected since they
   have no self-recursive calls. *)
let detect_non_forwarded_params (self_ref : GlobRef.t) (n_params : int)
    (body : Core.Expr.t) : int list =
  detect_non_forwarded_params_generic
    ~is_self_call:(fun _depth -> function
      | Core.Expr.Global {callee = r; _} -> globref_equal r self_ref
      | _ -> false )
    n_params body

(** What a binder a call's argument may name stands for, to
    {!partner_closure_params}: a closure ({!argument_source}), the function's
    parameter at a source position, or anything else. *)
type local_source = Local_closure | Local_param of int | Local_other

(** Where the type of [arg], passed by a function of [n_params] parameters
    for a callable, comes from, under the binders [locals] (innermost
    first): [`Param i] the function's parameter [i]'s; [`Closure] its own,
    new in each instantiation of the function -- a lambda, a local fixpoint
    or a partial application, which C++ writes as a lambda, has a closure
    type that depends on every parameter of the enclosing template, and an
    application or a [match] may compute one; [`Fixed] none of them -- a
    named global, a pattern variable or a literal has one type whatever
    instantiation of the function it is written in. *)
let rec argument_source n_params locals = function
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    argument_source n_params locals e
  | Core.Expr.Bound_variable {index = db; _} ->
    let depth = List.length locals in
    if db <= depth then
      match List.nth locals (db - 1) with
      | Local_closure -> `Closure
      | Local_param i -> `Param i
      | Local_other -> `Fixed
    else
      let i = n_params - (db - depth) in
      if i >= 0 && i < n_params then `Param i else `Fixed
  | Core.Expr.Global _
  | Core.Expr.Runtime_error _
  | Core.Expr.Erased_value _
  | Core.Expr.Axiom_value _
  | Core.Expr.UInt63 _
  | Core.Expr.Numeral _
  | Core.Expr.Float64 _
  | Core.Expr.String _
   |Core.Expr.Construct _ | Core.Expr.Tuple _ | Core.Expr.Persistent_array _ -> `Fixed
  | Core.Expr.Lambda _
  | Core.Expr.Apply _
  | Core.Expr.Let _
  | Core.Expr.Match _
  | Core.Expr.Fixpoint _
  | Core.Expr.Cofixpoint _ -> `Closure

(** For each member of the recursive groups [bodies], the source-order
    indices of the parameters a call from another member of its group passes
    a closure for, where that closure's type would feed the instantiation
    that makes it.  [callee self depth head] is the member the head of an
    application in the body of [self], under [depth] binders past its
    parameters, calls, if any: how a member names its partners is the
    caller's.

    A deduced callable is the argument's own type, and a closure written in
    a function template has a type of its own in each instantiation of it:
    [f<bool, L1>] calls [g<bool, L2>] with a lambda, and where [g] passes
    its callable back to [f], instantiates [f<bool, L2>], whose lambda is
    [L3], and so on without end.  Such a parameter is taken as a
    [crane::fn], a type that does not change.

    Whether it must be is a question about a graph whose nodes are the
    parameters of the group's members: a parameter depends on the parameter
    of the caller a call forwards to it, and on every parameter of a caller
    that passes it a closure.  A closure feeds its own maker exactly when its
    parameter reaches one of the maker's.  A parameter a partner passes a
    parameter of its own or a named function -- [g bool weight] -- keeps its
    deduced type, and so does one a closure reaches only to stop there --
    [g] calling back [f nat dbl m m]: the cycle of instantiations closes.  A
    parameter a self-call passes anything but itself is
    {!detect_non_forwarded_params}' to keep, and depends on nothing.  A
    self-call's closure is that function's too. *)
let closure_feedback_params ~callee bodies =
  let n_members = Array.length bodies in
  (* (callee, position) the parameter at each position of a member forwards
     to, and the (callee, position) each member passes a closure to. *)
  let forwards = Array.make n_members [] in
  let creates = Array.make n_members [] in
  let fixed = Array.make n_members [] in
  let add tbl r x = tbl.(r) <- x :: tbl.(r) in
  let scan self body =
    let params, body = collect_lams body in
    let n = List.length params in
    let strip = Core.Expr.strip_crossings in
    let rec walk locals e =
      match e with
      | Core.Expr.Apply {callee = f; arguments = args} ->
        ( match callee self (List.length locals) (strip f) with
        | Some g ->
          let self_call = Int.equal g self in
          List.iteri
            (fun k arg ->
              let source = argument_source n locals arg in
              if self_call && source <> `Param k then add fixed self k;
              match source with
              | `Param i -> add forwards self (i, (g, k))
              | `Closure -> add creates self (g, k)
              | `Fixed -> () )
            args
        | None -> () );
        walk locals f;
        List.iter (walk locals) args
      | Core.Expr.Lambda {body = b; _} -> walk (Local_other :: locals) b
      | Core.Expr.Let {value = e1; body = e2; _} ->
        walk locals e1;
        let bound =
          match argument_source n locals e1 with
          | `Param i -> Local_param i
          | `Closure -> Local_closure
          | `Fixed -> Local_other
        in
        walk (bound :: locals) e2
      | Core.Expr.Match {scrutinee = scrut; branches; _} ->
        walk locals scrut;
        Array.iter
          (fun {Core.Match.Branch.binders = ids; body = b; _} -> walk (List.map (fun _ -> Local_other) ids @ locals) b)
          branches
      | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
        let bodies = Core.Recursion.Group.bodies rec_group in
        let locals = List.init (Array.length bodies) (fun _ -> Local_closure) @ locals in
        Array.iter (walk locals) bodies
      | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.iter (walk locals) args
      | Core.Expr.Coerce {value = e; _}
      | Core.Expr.Boxed_value {value = e; _}
      | Core.Expr.Lambda_group_barrier {value = e; _} ->
        walk locals e
      | Core.Expr.Persistent_array {elements = elts; default = def} ->
        Array.iter (walk locals) elts;
        walk locals def
      | Core.Expr.Bound_variable _
      | Core.Expr.Global _
      | Core.Expr.Runtime_error _
      | Core.Expr.Erased_value _
      | Core.Expr.Axiom_value _
      | Core.Expr.UInt63 _
      | Core.Expr.Numeral _
      | Core.Expr.Float64 _
       |Core.Expr.String _ -> ()
    in
    walk [] body
  in
  Array.iteri scan bodies;
  let is_fixed (r, k) = List.mem k fixed.(r) in
  let succ (r, i) =
    List.filter_map (fun (j, dst) -> if j = i then Some dst else None) forwards.(r) @ creates.(r)
  in
  (* Whether some parameter of [maker] depends on [start]. *)
  let reaches_maker maker start =
    let rec go seen = function
      | [] -> false
      | node :: rest ->
        if List.mem node seen || is_fixed node then go seen rest
        else if Int.equal (fst node) maker then true
        else go (node :: seen) (succ node @ rest)
    in
    go [] [start]
  in
  let kept = Array.make n_members [] in
  Array.iteri
    (fun maker targets ->
      List.iter
        (fun ((g, k) as target) ->
          if
            (not (Int.equal g maker))
            && (not (is_fixed target))
            && (not (List.mem k kept.(g)))
            && reaches_maker maker target
          then add kept g k )
        targets )
    creates;
  Array.map (List.sort compare) kept

(** {!closure_feedback_params} of the top-level recursive groups of
    [struc]: a member calls a partner by name. *)
let partner_closure_params groups struc =
  let members = ref [] in
  Core_passes.Modutil.struct_iter
    (fun d ->
      List.iter
        (fun (fd : Core.Recursion.Definition.t) ->
          if Recursive_groups.group groups fd.entity <> None then
            members := (fd.entity, fd.body) :: !members )
        (Base.Core_util.term_defs d) )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let members = Array.of_list (List.rev !members) in
  let refs = Array.map fst members in
  let index g =
    let rec go i =
      if i >= Array.length refs then None else if Core.Ref.User.equal refs.(i) g then Some i else go (i + 1)
    in
    go 0
  in
  let kept =
    closure_feedback_params
      ~callee:(fun self _ f ->
        match f with
        | Core.Expr.Global {callee = g; _} when Recursive_groups.in_group groups refs.(self) g -> index g
        | _ -> None )
      (Array.map snd members)
  in
  let acc = ref [] in
  Array.iteri (fun i is -> if is <> [] then acc := (refs.(i), is) :: !acc) kept;
  !acc

(** {!closure_feedback_params} of the local fixpoint group [funs], whose
    member [j] a body of [n_params] parameters names, under [depth] binders,
    by [Core.Expr.Bound_variable (n_params + n_fix - j + depth)] ({!detect_non_forwarded_params_fix}):
    a lifted member deduces its callables as a top-level function does. *)
let local_fix_partner_closure_params funs =
  let n_fix = Array.length funs in
  let n_params = Array.map (fun f -> List.length (fst (collect_lams f))) funs in
  closure_feedback_params
    ~callee:(fun self depth f ->
      match f with
      | Core.Expr.Bound_variable {index = db; _} ->
        let j = n_params.(self) + n_fix + depth - db in
        if j >= 0 && j < n_fix then Some j else None
      | _ -> None )
    funs

(** For each member of the local fixpoint group [funs] lifted to a function
    template, the source-order indices of the callable parameters it takes
    as a [crane::fn] rather than deducing: those a self-call passes
    something else for ({!detect_non_forwarded_params_fix}) and those a
    partner passes a closure that flows back to it
    ({!local_fix_partner_closure_params}). *)
let lifted_fix_ungeneralised_params funs =
  let n_fix = Array.length funs in
  let partners = local_fix_partner_closure_params funs in
  Array.mapi
    (fun i f ->
      let lam_params, body = collect_lams f in
      detect_non_forwarded_params_fix (List.length lam_params) n_fix i body @ partners.(i) )
    funs

(** The source-order indices of the callable parameters, among the first
    [n_params], that a function made from [self_ref] takes as a [crane::fn]
    rather than generalising to [F &&]: those a self-call passes something
    else for (see {!detect_non_forwarded_params}), those a partner's call
    passes a closure for (see {!partner_closure_params}), and those a closure
    holds on to (see {!escaping_params}).  A free function and a method of an
    inductive are generalised alike. *)
let ungeneralised_callable_params cx ~self_ref ~suspended n_params body =
  let partners =
    List.filter
      (fun i -> i < n_params)
      (Option.default [] (Core.Ref.User.Map.find_opt self_ref cx.ctx.input.program.partner_closure_params))
  in
  Escape.IntSet.of_list
    (detect_non_forwarded_params self_ref n_params body
    @ partners
    @ escaping_params cx ~suspended n_params body)

(** {!ungeneralised_callable_params} for the definition of [r] at type [ty]
    with body [b], over the parameters {!Base.Type_util.declared_parameters}
    finds, written or eta-expanded: the ones its function is generated
    with. *)
let ungeneralised_callables_of_definition cx r ty b =
  let params, body = declared_parameters ty b in
  ungeneralised_callable_params cx ~self_ref:r
    ~suspended:(Base.Table.is_coinductive_type (core_return_type ty))
    (List.length params) body

(** Whether a function takes a callable parameter of C++ type [f] as a
    deduced [F &&] rather than a [crane::fn]: unless the parameter is
    [kept_as_fn] -- in {!ungeneralised_callable_params}' set, a fact about the
    binder decided where its source position is known -- or [f] erased to
    [std::any] throughout in a signature whose deducible type variables
    [primary] are none.  A callable deduced there pins nothing down, and the
    template it forces costs the definition its use as a value of the type
    its Rocq signature names ([church]). *)
let generalises_callable ~kept_as_fn ~primary f =
  (not kept_as_fn) && not (IntSet.is_empty primary && is_fully_erased_fun_ty f)
