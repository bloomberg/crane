(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Monadic and unit-valued Core and the C++ it becomes: the effect
    operation a use heads, whether a call is a [void] statement rather than
    a value, [tt] and the unit-to-void conversion, and the reified [ITree]
    types and [ret] builders.  Below type conversion, which asks it how a
    monadic parameter is reified. *)

open Names
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query

(** Extract the innermost result type from a (possibly monadic) Core type.
    For [nat -> itree ioE unit], returns [unit].
    For [nat -> unit], returns [unit].
    For [itree ioE unit] (zero-arg monadic), returns [unit].
    The result type is always the LAST type argument of the monad
    (monads parameterize on the result type as their last type param). *)
let core_result_type ty =
  let cod = core_codomain ty in
  match cod with
  | Core.Type.Global_app {head = r; type_arguments = args; _} when Base.Table.is_monad r ->
    (match List.rev args with r :: _ -> r | [] -> cod)
  | _ -> cod

(** Check if a monad reference uses the reified ITree extraction mode
    (i.e. its monad template string contains ["ITree"]).

    Lives in {!Base.Table} because {!Base.Type_util} asks it too, to recognise an
    event family. *)
let is_monad_reified = Base.Table.is_monad_reified

(** The effect operation the use [use] heads, as Core elaborated it
    ({!Core_plan.Effects}): its operation, and the mode it is generated in, read
    from the unit's facts, set before anything is planned
    ({!Lowering_state.unit_facts}).  One the analysis did not reach heads
    none.  Under [CRANE_CHECK_IR] both are checked against what the global's
    registration and the mode of the generation translating it would say. *)
let effect_of cx (use : Core.Global_use.t) =
  let found = Core_plan.Effects.lookup cx.ctx.input.unit.effects use in
  if Option.has_some found then Core_plan.Effects.tally ();
  if Base.Probe.checking () then begin
    let here =
      Option.map
        (fun operation -> {Core_plan.Effects.operation; mode = cx.ctx.input.itree_mode})
        (Core_plan.Effects.operation_of use.callee)
    in
    match (found, here) with
    | Some e, here when here <> Some e ->
      Base.Probe.violation "effect operations"
        Pp.(
          str "an effect operation of " ++ str (Base.Table.kername_of_global use.callee)
          ++ str " elaborated from Core disagrees with the generation translating it")
    | None, Some _ ->
      Base.Probe.violation "effect operations"
        Pp.(
          str "an effect operation of " ++ str (Base.Table.kername_of_global use.callee)
          ++ str " is translated where Core did not reach it")
    | _ -> ()
  end;
  found

(** Whether the use [use] heads the effect operation [op]. *)
let is_effect cx op use =
  match effect_of cx use with Some e -> e.Core_plan.Effects.operation = op | None -> false

(** Whether the use [use] heads the effect operation [op], generated in
    {!Core_plan.Effects.Sequential} mode. *)
let is_sequential_effect cx op use =
  match effect_of cx use with
  | Some {Core_plan.Effects.operation; mode = Sequential} -> operation = op
  | _ -> false

(** Apply unit-to-void conversion on a C++ type.  [unit_void] comes from
    {!core_type_is_void_call}, which already declines for a reified monad, so
    there is one outcome left: the whole type is [void]. *)
let apply_unit_void unit_void (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t = if unit_void then Void else ty

(** Generate the C++ expression for Rocq's [tt] (the unit constructor).
    Does NOT call [gen_expr] — it checks the extraction table directly. *)
let mk_tt_expr () : Cpp_ir.Lowered.Expr.t =
  match Base.Table.resolve_tt_ctor () with
  | Some tt_ref when Base.Table.is_custom tt_ref -> mk_cppglob tt_ref []
  | Some tt_ref ->
    let ind_ref, ctor_name =
      match tt_ref with
      | GlobRef.ConstructRef ((kn, i), cidx) ->
        (GlobRef.IndRef (kn, i), Id.of_string (Base.Common.enum_ctor_name_of_ref kn i cidx))
      | _ -> CErrors.anomaly (Pp.str "mk_tt_expr: tt is not a ConstructRef")
    in
    Enum_value (ind_ref, ctor_name)
  | None -> CErrors.anomaly (Pp.str "mk_tt_expr: could not resolve core.unit.tt")

(** Whether [ty]'s codomain is a monad extracted as a reified tree. *)
let codomain_is_reified_monad (ty : Core.Type.t) : bool =
  match core_codomain ty with
  | Core.Type.Global_app {head = r; _} -> Base.Table.is_monad r && is_monad_reified r
  | _ -> false

(** Whether [ty] is the type of something whose C++ call returns [void]: a
    function (or monad) whose result type is [unit].  Such a call cannot be
    used as a value — it must be wrapped in an IIFE that executes it for its
    side effect and returns [std::monostate{}].

    A monad counts only in sequential mode, where a monadic value {e is} the
    running of its effects and a [unit] result is therefore nothing.  Under the
    reified backend it is data: [itree E unit] is a tree that has to be
    returned, built, and bound into, and void-ifying it does not merely mistype
    the call -- it drops the tree, and with it the sequencing the program was
    expressed in. *)
let core_type_is_void_call (ty : Core.Type.t) : bool =
  (match Base.Type_util.resolve_meta ty with
  | Core.Type.Arrow _ -> true
  | Core.Type.Global_app {head = r; _} -> Base.Table.is_monad r
  | _ -> false)
  && core_type_is_unit (core_result_type ty)
  && not (codomain_is_reified_monad ty)

(** Whether a global reference [r] has been void-ified.

    An inline custom is void-ified in reified mode as well.  Its replacement
    text is written once, in the sequential spelling -- [std::cout << s] is a
    statement, not a tree -- so its Rocq type saying [itree E unit] does not
    make its C++ a tree.  The lift into [ITree<R>::ret()] at the call site is
    what makes it one, and that lift is keyed on this. *)
let is_void_ified_ref (r : GlobRef.t) : bool =
  match find_type_opt r with
  | Some ty ->
    core_type_is_void_call ty
    || Base.Table.is_inline_custom r
       && core_type_is_unit (core_result_type ty)
       && codomain_is_reified_monad ty
  | None -> false

(** Wrap a void-returning function call expression in an IIFE so it can
    be used in value context.  Produces:
      [&]() { void_call(); return std::monostate{}; }()
    The call is executed for side effects; the IIFE returns the unit value. *)
let wrap_void_call_as_value (call_expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  Cpp_ir.Build.iife None [Expression call_expr; Return (Some (mk_tt_expr ()))]

(** Check whether a Core function expression [f] in [Core.Expr.Apply(f, args)] would
    produce a void-returning call in C++.  Handles:
    - [Core.Expr.Global(r, _)]  — named function, look up type in extraction table
    - [Core.Expr.Bound_variable(i)]       — variable (e.g. callback), look up type in env
    - [Core.Expr.Coerce]/[Core.Expr.Boxed_value]/[Core.Expr.Lambda_group_barrier] — transparent wrapper, recurse *)
let rec core_callee_is_void cx = function
  (* A record field of a [unit]-returning function type is stored as a
     [std::function<void(...)>]: [globals_object.(globals_set) gs]. *)
  | Core.Expr.Global {callee = r; _} when Base.Table.is_projection r -> (
    try core_type_is_void_call (Base.Table.find_type r) with Not_found -> false )
  | Core.Expr.Global {callee = r; _} -> is_void_ified_ref r
  | Core.Expr.Coerce {value = inner; _}
  | Core.Expr.Boxed_value {value = inner; _}
  | Core.Expr.Lambda_group_barrier {value = inner; _} ->
    core_callee_is_void cx inner
  | Core.Expr.Bound_variable {index = i; _} -> ( try core_type_is_void_call (get_env_type cx i) with _ -> false )
  | _ -> false

(** Whether the C++ for a Core expression is a statement rather than a value:
    a call to something void-ified, applied or not. *)
let core_expr_is_void_call cx = function
  | Core.Expr.Apply {callee = f; _} -> core_callee_is_void cx f
  | e -> core_callee_is_void cx e

(** Whether a Core expression in a value position may compile to a [void] call,
    and so has to be wrapped by {!wrap_void_call_as_value}: a call to something
    void-ified, or a match whose every branch is one -- the projection
    extraction writes [r.(f) x] as, applying a field binder of a
    [unit]-returning function type, stored as [std::function<void(...)>]. *)
let rec core_value_is_void_call cx = function
  | Core.Expr.Apply {callee = f; _} -> core_callee_is_void cx f
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    core_value_is_void_call cx e
  | Core.Expr.Match {branches = pv; _} ->
    Array.length pv > 0
    && Array.for_all
         (fun {Core.Match.Branch.binders = binds; body = body; _} ->
           let applies_void_binder = function
             | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = k; _}; _} when k >= 1
               && k <= List.length binds -> (
               match List.nth_opt binds (List.length binds - k) with
               | Some (_, ty) -> core_type_is_void_call ty
               | None -> false )
             | e -> core_value_is_void_call cx e
           in
           match body with
           | Core.Expr.Coerce {value = b; _}
           | Core.Expr.Boxed_value {value = b; _}
           | Core.Expr.Lambda_group_barrier {value = b; _} ->
             applies_void_binder b
           | b -> applies_void_binder b )
         pv
  | _ -> false

(** {3 Reified ITree helpers}

    In reified mode, [itree E R] extracts to [std::shared_ptr<ITree<R>>]
    instead of being erased to [R].  The helpers below build C++ AST nodes
    for ITree types and constructors, and detect whether a Core expression
    already carries a reified tree value. *)

(** Extract the result type [R] from a monadic Core type [itree E R].
    Returns the second non-erased type argument, or [Core.Type.Unknown] if
    the type does not have the expected shape. *)
let extract_itree_result_core (core_ty : Core.Type.t) : Core.Type.t =
  match resolve_meta core_ty with
  | Core.Type.Global_app {type_arguments = _ :: r :: _; _} -> r
  | _ -> Core.Type.Unknown

(** Build the C++ type [std::shared_ptr<ITree<r_cpp>>]. *)
let mk_itree_type (r_cpp : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  Shared_pointer (External (Cpp_ir.Crane_rt.itree, [r_cpp]))

(** Build a call of [ITree<R>::ret(...)].
    When [r_cpp] is [void], generates [ITree<void>::ret()]. *)
let mk_itree_ret (r_cpp : Cpp_ir.Lowered.Type.t) (args : Cpp_ir.Lowered.Expr.t list) : Cpp_ir.Lowered.Expr.t =
  let itree_ty : Cpp_ir.Lowered.Type.t = External (Cpp_ir.Crane_rt.itree, [r_cpp]) in
  Cpp_ir.Build.call (Type_member (itree_ty, Id.of_string "ret")) args

(** Build [ITree<R>::ret(v)], or [ITree<void>::ret()] where there is no value
    to carry.  [r_cpp] is the C++ result type, [r_core] the Core one, [v] the value.

    Only a type extracted as C++ [void] is valueless.  Rocq's [unit] is not: it
    has an inhabitant, spelled [std::monostate], and a tree carrying it is a
    tree like any other.  Spelling it [ITree<void>] instead loses the
    distinction between a computation that yields nothing and one that yields
    the trivial thing, and the two then meet in one match. *)
let mk_itree_ret_for_value (r_cpp : Cpp_ir.Lowered.Type.t) r_core v =
  if r_cpp = Void || core_type_is_void r_core then mk_itree_ret Void [] else mk_itree_ret r_cpp [v]

(** Reify a monadic parameter type for ITree extraction.

    In reified mode, the C++ type for a monadic parameter [itree E R] after
    monad erasure is just [R].  This function wraps it back into
    [shared_ptr<ITree<R>>] so the tree can be passed as a first-class value.
    Does nothing in sequential mode or when [core_ty] is not monadic. *)
let reify_monadic_param_type cx core_ty (cpp_ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  if is_monadic_core_type core_ty && cx.ctx.input.itree_mode = Reified then begin
    let r_ty : Cpp_ir.Lowered.Type.t =
      match cpp_ty with
      | Entity_application (_, _ :: r :: _, _) -> r
      | t -> t
    in
    Shared_pointer (External (Cpp_ir.Crane_rt.itree, [r_ty]))
  end
  else cpp_ty

(** Check whether a Core expression already produces a reified monadic value
    (a [shared_ptr<ITree<R>>]).  A local whose type is monadic is one, and
    so is [Core.Expr.Apply(Core.Expr.Bound_variable f, args)] where [f] is a local function whose return
    type is monadic.  Such calls already return a tree, so wrapping in
    [ITree::ret()] would incorrectly double-wrap.

    Also covers a constructor of the monad type itself: [ITree]'s own node
    constructors are extracted to expressions that build a tree, so a term
    like [go (RetF x)] is already the tree and must not be wrapped again.

    A call to a global counts too, but only where Crane itself wrote the
    callee: a global with a mapping (e.g. [print_endline]) stands for a direct
    C++ expression, which genuinely needs the wrap, and a void-ified one
    returns nothing at all in C++ however monadic its Rocq type reads.  The
    exception is a mapping whose result is a {e reified} monad: that monad's
    values are trees, so its mappings -- [itree_trigger], [itree_ret] -- are
    spelled as expressions that build one, and wrapping would double it. *)
let rec is_reified_monadic_expr cx core_expr =
  (* The result of applying [n] arguments to something of Core type [ty].  A
     dummy domain is an erased type parameter, which the term does not pass, so
     it is stepped over without spending an argument; an alias still owed
     arguments is the arrows it names ([stateT S M T] is [S -> M (S * T)]). *)
  let rec core_result_after n ty =
    match Base.Type_util.resolve_meta ty with
    | Core.Type.Arrow {parameter = dom; result = res} when (match Base.Type_util.resolve_meta dom with
            | Core.Type.Erased _ -> true
            | _ -> false) ->
      core_result_after n res
    | Core.Type.Arrow {result = res; _} when n > 0 -> core_result_after (n - 1) res
    | Core.Type.Global_app _ as t when n > 0 -> (
      match Base.Type_util.expand_core_fun_alias t with
      | Core.Type.Arrow _ as f -> core_result_after n f
      | _ -> t )
    | t -> t
  in
  (* A callee generic over a monad class returns [m (list B)]: a [Core.Type.Variable_app] headed
     by the class's carrier variable, which no test against a concrete monad
     glob can recognise.  The monad is nonetheless known {e here} -- the call
     supplies the dictionary, and the instance the emitter writes for it is
     [Monad_itree<std::any>] -- so the question is put to the call site rather
     than to the callee's type, which is the only side that does not know the
     answer.

     The dictionary is identified by the domain it fills: a class applied to
     the very carrier the result is headed by.  An instance passed for another
     class, or for another carrier, says nothing about this result. *)
  let instance_carrier_is_reified g =
    match Option.map core_codomain (find_type_opt g) with
    | Some t -> (
      match Base.Type_util.resolve_meta t with
      | Core.Type.Global_app {type_arguments = targs; _} ->
        List.exists
          (fun t ->
            match Base.Type_util.resolve_meta t with
            | Core.Type.Global_app {head = m; _} -> Base.Table.is_monad m && is_monad_reified m
            | _ -> false )
          targs
      | _ -> false )
    | None -> false
  in
  let reified_via_dictionary ty args head =
    (* A carrier of arrow kind stands in its class's argument list as the
       [Core.Type.Variable_app] it would be if applied, with nothing applied to it yet. *)
    let names_carrier t =
      match Base.Type_util.resolve_meta t with
      | Core.Type.Variable {variable = i; _} | Core.Type.Variable_app {head = i; _} -> Int.equal i head
      | _ -> false
    in
    let rec go doms args =
      match (doms, args) with
      | dom :: doms', _ when erased_by_extraction dom -> go doms' args
      | dom :: doms', a :: args' ->
        let fills_this_carrier =
          match Base.Type_util.resolve_meta dom with
          | Core.Type.Global_app {type_arguments = targs; _} -> List.exists names_carrier targs
          | _ -> false
        in
        ( match a with
        | Core.Expr.Global {callee = g; _} when fills_this_carrier ->
          instance_carrier_is_reified g
        | _ -> go doms' args' )
      | _ -> false
    in
    go (Base.Type_util.core_domains ty) args
  in
  (* A local's type may say nothing -- a rank-2 [D ~> itree E] parameter is
     erased, so what it returns is a type variable -- and then the Rocq
     typing of the position is the only statement there is: an argument at a
     monadic parameter has that monadic type, and every value of a reified
     monad is a tree.  Only a type that says something else is evidence of a
     plain value. *)
  let says_monadic ty =
    Option.has_some (Base.Type_util.type_monad ty)
    ||
    match Base.Type_util.resolve_meta ty with
    | Core.Type.Variable _ | Core.Type.Unknown | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
    | _ -> false
  in
  match core_expr with
  (* A coercion changes the type a value is read at, not whether it is a
     tree: the question is asked of what is under it. *)
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    is_reified_monadic_expr cx e
  | Core.Expr.Apply
    {callee =
      (Core.Expr.Coerce {value = f; _} | Core.Expr.Boxed_value {value = f; _}
        | Core.Expr.Lambda_group_barrier {value = f; _});
                     arguments = args} ->
    is_reified_monadic_expr cx (Core.Expr.Apply {callee = f; arguments = args})
  | Core.Expr.Bound_variable {index = i; _} ->
    (match get_env_type_opt cx i with Some ty -> says_monadic ty | None -> false)
  | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; _}; arguments = args} ->
    (match get_env_type_opt cx i with
     | Some ty -> says_monadic (core_result_after (List.length args) ty)
     | None -> false)
  (* A global of monadic type is already a tree whether or not it is applied:
     a zero-arity constant like [get : itree E nat] is the same value that its
     applied form would be, and wrapping it in [ret] builds a tree of trees. *)
  | Core.Expr.Global {callee = r; _} | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; _} ->
    let nargs = match core_expr with Core.Expr.Apply {arguments = args; _} -> List.length args | _ -> 0 in
    (not (is_void_ified_ref r))
    && ( match find_type_opt r with
       | Some ty ->
         let res = core_result_after nargs ty in
         ( match Base.Type_util.resolve_meta res with
         | Core.Type.Variable_app {head; _} ->
           let args = match core_expr with Core.Expr.Apply {arguments = args; _} -> args | _ -> [] in
           reified_via_dictionary ty args head
         | _ -> (
           match Base.Type_util.type_monad res with
           | Some m -> (not (Base.Table.is_inline_custom r)) || is_monad_reified m
           | None -> false ) )
       | None -> false )
  | Core.Expr.Construct {result_type = ty; _} -> is_monadic_core_type ty
  | _ -> false
