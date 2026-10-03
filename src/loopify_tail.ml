(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Tail-recursion loopification for {!Loopify}: the [while] rewrite, the
    generic return-statement rewriter, shadow variables, and the expression
    decompositions the other strategies build on. *)

open Names
open Minicpp
open Loopify_analysis

(** {2 Tail recursion transformation}

    A [_continue] flag drives the while condition.  Each dispatch arm either
    assigns [_result] and clears the flag, which leaves the loop, or updates
    the shadow parameters and leaves the flag set.

    {[
      RetType _result\{\};
      auto _loop_x = x; auto _loop_l = l;
      bool _continue = true;
      while (_continue) \{
        auto &&_sv = _loop_l->v();
        if (std::holds_alternative<Base>(_sv)) \{
          _result = base_val; _continue = false;
        \} else \{
          _loop_x = new_x; _loop_l = new_l;
        \}
      \}
      return _result;
    ]} *)

(** Create a shadow variable name for tail-recursion loop variables.
    Prefixes [id] with [_loop_], avoiding C++'s reserved double-underscore. *)
let shadow_name (id : Id.t) : Id.t =
  let s = Id.to_string id in
  (* Avoid double underscores (reserved in C++): _loop_ + _self → _loop_self *)
  if String.length s > 0 && s.[0] = '_' then
    Id.of_string ("_loop" ^ s)
  else
    Id.of_string ("_loop_" ^ s)

(** Strip reference and const modifiers from a type, converting it to a value
    type suitable for local variable declarations. [const shared_ptr<T> &]
    becomes [shared_ptr<T>], and [F0 &&] ([Tref (Forwarding, Tvar)]) becomes [Tvar].
*)
let rec strip_ref_type = function
  | Tref (_, t) -> strip_ref_type t
  | t -> t

(** Strip reference types AND const modifiers from a type. Used for shadow
    variables in tail recursion, which must be mutable to support reassignment
    in the loop body.  However, [const] on a pointer pointee is preserved:
    [const tree *] stays [const tree *] because the pointer variable itself is
    mutable (can be reassigned), while the [const] just prevents modification
    through the pointer — removing it would break [_loop_self = this] when
    [this] is [const T *] in a const method. *)
let rec strip_ref_and_const_type = function
  | Tref (_, t) -> strip_ref_and_const_type t
  | Tconst (Tptr _) as t -> t
  | Tconst t -> strip_ref_and_const_type t
  | t -> t

(** Return [true] when a parameter type can be safely moved into a shadow
    variable.  References cannot be moved from; const values would trigger
    a pessimizing-move warning since the move constructor receives [const T&&]
    and falls back to copy anyway. *)
let is_moveable_param_type = function
  | Tref _ -> false
  | Tconst _ -> false
  | _ -> true

(** Extract the pointee type from a "borrowed value-type" parameter.

    A borrowed value-type parameter is one declared as [const T&] where [T] is a
    value-type inductive.  These can be optimised to [const T*] shadows that
    avoid copying the entire value at each loop iteration.

    Under [Crane Reuse] an owned by-value parameter qualifies too.  Reuse needs
    the scrutinee owned (that is what gives the loop cells it may recycle), and
    escape analysis therefore passes it by value; without this case the shadow
    would be a [T] and every iteration would copy the whole node -- strictly
    worse than the borrow it replaced.  A by-value parameter lives for the whole
    call, so a pointer into it (or into a subterm it keeps alive) is as safe as
    one into a [const T&].  Which parameters may actually be walked by pointer
    is decided separately by {!tail_pointer_safe_flags}: an accumulator that is
    rebuilt each iteration ([acc := Cons(x, acc)]) is not pointer-safe and keeps
    its value shadow.

    @return [Some pointee_type] when the parameter qualifies, [None] otherwise *)
let borrowed_value_param_pointee = function
  | Tref (Lvalue, Tconst t) when is_value_type_ret t -> Some t
  | Tconst (Tref (Lvalue, t)) when is_value_type_ret t -> Some t
  | t when Table.reuse () && Table.non_atomic_rc () && is_value_type_ret t ->
    Some t
  | _ -> None

(** Extract the underlying type variable id from a forwarding-reference type.
    [Tref (Forwarding, Tvar (Tv_index (_, Some id) | Tv_named id))] → [Some id] *)
let rec extract_fwd_ref_tvar = function
  | Tref (_, inner) -> extract_fwd_ref_tvar inner
  | Tvar (Tv_index (_, Some id) | Tv_named id) -> Some id
  | _ -> None

(** The arrow a template parameter is constrained to, when it is a callable one.
    [tparams] holds [(kind, name)] pairs from the surrounding template header;
    a [TTfun (dom, cod)] kind is what becomes the
    [std::is_invocable_r_v<cod, F &, dom &...>] clause. *)
let lookup_tparam_fun_type tparams id =
  let name = Id.to_string id in
  List.find_map
    (fun (tt, tparam_id) ->
      match tt with
      | TTfun (dom, cod) when String.equal (Id.to_string tparam_id) name ->
        Some (Tfun (dom, cod))
      | _ -> None )
    tparams

(** Compute the shadow variable type for a tail-recursive loop.

    When [pointer_safe] is [true] and the parameter is a borrowed value-type
    ([const T&] where [T] is a value-type inductive), the shadow becomes
    [const T*] (raw pointer).

    A callable parameter arrives as a deduced template parameter — the caller's
    closure type — and a shadow exists only because the back edge reassigns it.
    Those two facts cannot both hold of one variable: a closure type has exactly
    one value, so nothing the loop builds is assignable to it.  The shadow has
    to be a type that can hold every callable the loop puts in it, which is the
    arrow the parameter's constraint already states.

    Otherwise the shadow inherits the parameter's type verbatim. *)
let tail_shadow_type ~tparams ~pointer_safe ty =
  match (pointer_safe, borrowed_value_param_pointee ty) with
  | true, Some t -> Tptr (Tconst t)
  | _ ->
    ( match Option.bind (extract_fwd_ref_tvar ty) (lookup_tparam_fun_type tparams) with
    | Some arrow -> arrow
    | None -> ty )

(** Generate the initialiser expression for a shadow variable.

    - Pointer-safe shadows: [& orig_id] (address-of)
    - Moveable parameters: [std::move(orig_id)]
    - Otherwise: plain copy *)
let tail_shadow_init orig_id shadow_ty ty =
  match shadow_ty, borrowed_value_param_pointee ty with
  | Tptr _, Some _ -> CPPunop (Uaddr, CPPvar orig_id)
  | _ ->
    if is_moveable_param_type ty then CPPmove (CPPvar orig_id)
    else CPPvar orig_id

(** Adjust a recursive-call argument to match the shadow variable's type.

    - When the shadow is a pointer and the argument is [*shadow_var]
      (i.e., dereference of one of our own pointer-safe shadows): just use
      [shadow_var] directly since it is already a raw pointer.
    - When the shadow is a pointer and the argument is [*ptr]: use
      [crane_raw(ptr)] (works whether [ptr] is a smart pointer or already raw,
      as under [Crane Arena])
    - When the shadow is a pointer and the argument is a variable: [&arg]
    - Otherwise: pass through unchanged

    @param shadow_ids  Set of shadow variable IDs (already raw pointers) *)
let tail_shadow_arg ~shadow_ids shadow_ty arg =
  match shadow_ty, arg with
  | Tptr _, CPPderef (CPPvar id) when List.exists (Id.equal id) shadow_ids ->
    CPPvar id
  | Tptr _, CPPderef inner ->
    CPPfun_call (call_opaque, CPPrt Crane_rt.Raw, of_reversed ([inner]))
  | Tptr _, CPPvar _ -> CPPunop (Uaddr, arg)
  | _ -> arg

(** Provenance of a local binder: the loop *parameter* whose storage the binder
    lives inside, or [None] when the binder was produced locally (a freshly
    built value, a computed match scrutinee, an inlined callee's temporary...).

    This is what makes a [const T*] shadow safe or not.  Deciding pointer-safety
    from the *shape* of a recursive-call argument alone ([*a1] "looks like" a
    borrow) says nothing about whose storage [a1] points into.  If [a1] is a
    field of a *different* loop variable that the same iteration overwrites, or
    of a block-scoped temporary, the pointer dangles before the next iteration
    reads it.  Only a pointer that walks deeper into the parameter's *own*
    borrowed argument is guaranteed to stay live: that storage belongs to the
    caller and nothing in the loop can drop it.

    Binders bound more than once with conflicting roots (pattern variables such
    as [a1] are reused across match branches) are demoted to [None]: this is a
    flow-insensitive over-approximation, so it can only cost an optimisation,
    never soundness. *)
let compute_binder_provenance params body =
  let param_ids = List.map fst params in
  let is_param x = List.exists (Id.equal x) param_ids in
  let tbl : (Id.t * Id.t option) list ref = ref [] in
  let record id p =
    match List.assoc_opt id !tbl with
    | None -> tbl := (id, p) :: !tbl
    | Some q ->
      if not (Option.equal Id.equal q p) then
        tbl := (id, None) :: List.remove_assoc id !tbl
  in
  let rec prov_of = function
    | CPPvar x ->
      if is_param x then Some x
      else (match List.assoc_opt x !tbl with Some p -> p | None -> None)
    | CPPderef e | CPPmove e | CPPaccess (Adot, e, _) | CPPaccess (Aarrow, e, _)
    | CPPget (e, _) | CPPget' (e, _, _) | CPPunop (_, e) ->
      prov_of e
    | CPPfun_call (_, CPPrt Crane_rt.Raw, {rev = [e]}) -> prov_of e
    (* [x.v()] / [std::get<K>(e)]: projections that stay inside [e]'s storage. *)
    | CPPfun_call (_, CPPaccess (Adot, e, _), {rev = []})
     |CPPaccess_call (Aarrow, e, _, []) ->
      prov_of e
    | CPPstd_get (_, Some e) -> prov_of e
    | _ -> None
  in
  let rec walk_stmt s =
    match s with
    | Sasgn (id, _, e) -> record id (prov_of e)
    | Smatch (scrut, branches, default) ->
      let root = prov_of scrut.sc_expr in
      List.iter
        (fun br ->
          Option.iter (fun v -> record v root) br.smb_var;
          List.iter (fun (fid, _, _) -> record fid root) br.smb_field_bindings;
          List.iter walk_stmt br.smb_body)
        branches;
      Option.iter (List.iter walk_stmt) default
    | s -> iter_stmt_children ~on_expr:(fun _ -> ()) ~on_stmts:(List.iter walk_stmt) s
  in
  (* Two sweeps: a binder may be recorded after a use that reads it. *)
  List.iter walk_stmt body;
  List.iter walk_stmt body;
  prov_of

(** Compute pointer-safety flags for each parameter.

    A parameter is "pointer-safe" when it is a borrowed value-type ([const T&]),
    every recursive call site passes either [*ptr] or the same variable back as
    that argument, *and* that argument's storage provably belongs to the
    parameter itself (see {!compute_binder_provenance}).  Together these
    guarantee the pointer shadow will always point at a live object.

    When [binding_env] is supplied, [CPPvar x] at a call site is accepted as
    pointer-safe if [x] is bound to [CPPderef _] in that environment — i.e., if
    the caller wrote [x = *(sp)] and then passed [x] instead of [*(sp)] directly.
    This handles the common case where translation.ml introduces an intermediate
    binding to deduplicate multi-use values.

    @return A bool list parallel to [params]: [true] = can use [const T*] shadow *)
let tail_pointer_safe_flags check params body ?(binding_env = []) () =
  let calls = collect_stmts check ~in_visitor:false body in
  if calls = [] then
    List.map (fun _ -> false) params
  else
    let is_safe_arg id arg =
      match arg with
      | CPPderef _ -> true
      | CPPvar arg_id when Id.equal arg_id id -> true
      | CPPvar x ->
        (* Look through: if x = *(sp) in scope, treat as CPPderef *)
        (match List.assoc_opt x binding_env with
         | Some (CPPderef _) -> true
         | _ -> false)
      | _ -> false
    in
    let prov_of = compute_binder_provenance params body in
    List.mapi
      (fun i (id, ty) ->
        match borrowed_value_param_pointee ty with
        | None -> false
        | Some _ ->
          List.for_all
            (fun cs ->
              match List.nth_opt cs.cs_args i with
              | Some arg ->
                (* Shape alone is not enough: the pointee must live inside this
                   parameter's own borrowed argument, or it can be freed by the
                   very iteration that publishes the pointer. *)
                is_safe_arg id arg
                && (match prov_of arg with
                    | Some root -> Id.equal root id
                    | None -> false)
              | None -> false)
            calls)
      params

(** Rewrite references to pointer-safe shadow variables ([const T*]) so that
    reads dereference the pointer and method calls use [->] via
    [CPPaccess_call].

    Pointer-safe shadows store a [const T*] instead of copying the value.
    Code originally written against [const T&] needs adjustment:
    - Bare variable access [id] becomes [*id]
    - Member calls [id.method(args)] become [id->method(args)]
    - Direct assignments [id = rhs] keep the LHS undereferenceed (the
      pointer itself is being reassigned)
    - Pattern-match scrutinees involving a pointer shadow suppress the
      value-type flag to avoid incorrect deref codegen

    @param shadow_params The shadow parameter list; only entries whose type
                         is [Tptr _] are considered pointer-safe
    @param stmts         Statement list to rewrite
    @return Rewritten statements with pointer dereferences inserted *)
let rewrite_borrowed_shadow_uses shadow_params stmts =
  let ptr_shadows =
    List.filter_map
      (fun (id, ty) -> match ty with Tptr _ -> Some id | _ -> None)
      shadow_params
  in
  let is_ptr_shadow id = List.exists (Id.equal id) ptr_shadows in
  let expr_mentions_ptr_shadow e =
    expr_exists (function CPPvar id when is_ptr_shadow id -> true | _ -> false) e
  in
  let rec expr = function
    | CPPfun_call (_, CPPaccess (Adot, CPPvar id, meth), args)
      when is_ptr_shadow id ->
      (* A method call's arguments are in source order, a function call's are
         not: the reversal has to come off here. *)
      CPPaccess_call (Aarrow, CPPvar id, meth, List.map expr (call_args args))
    | CPPvar id when is_ptr_shadow id -> CPPderef (CPPvar id)
    | e -> map_expr expr stmt Fun.id e
  and stmt = function
    | Sexpr (CPPbinop (Bassign, CPPvar id, rhs)) when is_ptr_shadow id ->
      (* Assignment to a pointer shadow: keep the LHS as a raw pointer
         (don't dereference it), only rewrite the RHS. *)
      Sexpr (CPPbinop (Bassign, CPPvar id, expr rhs))
    | Smatch (scrut, branches, default) ->
      (* A scrutinee already reached through a pointer shadow keeps its own
         spelling, and is a pointer rather than a value. *)
      let ptr_scrutinee = expr_mentions_ptr_shadow scrut.sc_expr in
      Smatch
        ( { scrut with
            sc_expr =
              (if ptr_scrutinee then scrut.sc_expr else expr scrut.sc_expr);
            sc_access = (if ptr_scrutinee then Aarrow else scrut.sc_access) },
          List.map
            (fun br ->
              { br with
                smb_extra_conds = List.map expr br.smb_extra_conds;
                smb_body = List.map stmt br.smb_body })
            branches,
          Option.map (List.map stmt) default )
    | s -> map_stmt expr stmt Fun.id s
  in
  List.map stmt stmts

(** Wrap [e] in [std::move] only when it is an lvalue (a plain variable
    reference).  Wrapping rvalues (function calls, literals, binary ops) in
    [std::move] is a pessimising move — it prevents copy elision on the
    assignment and is rejected by [-Wpessimizing-move]. *)
let move_if_lvalue = function
  | CPPvar _ as e -> CPPmove e
  | e -> e

(** Assign [expr] to the [_result] accumulator variable.
    Generates the statement list [[\[_result = expr;\]]]. *)
let assign_result expr =
  [Sexpr (CPPbinop (Bassign, CPPvar (id_result), move_if_lvalue expr))]

(** Return [expr] directly from the tail-recursion while loop.
    Used only in tail-recursion rewriting. *)
let assign_result_and_stop expr =
  [ Sreturn (Some (move_if_lvalue expr)) ]

(** Generate temp-based parameter updates to avoid read-after-write hazards. For
    a recursive call like [f b (a mod b)], we must evaluate all argument
    expressions (which reference _loop_ variables) before overwriting any of
    them. We emit: auto _next_a = expr_for_a; auto _next_b = expr_for_b; _loop_a
    = std::move(_next_a); _loop_b = std::move(_next_b);

    Self-assignments (_loop_x = _loop_x) are skipped entirely. When there is
    only one non-trivial assignment the temps are unnecessary but harmless.

    [CPPderef] arguments (advancing a list tail via [*(d_a1)]) are NOT moved
    because the deref target may be through a shared_ptr whose pointee is
    aliased by the caller. *)
let make_shadow_updates shadow_params args =
  let shadow_ids = List.map (fun (id, _) -> id) shadow_params in
  let is_self_assign shadow_id arg =
    match arg with
    | CPPvar id when Id.equal id shadow_id -> true
    | CPPmove (CPPvar id) when Id.equal id shadow_id -> true
    | _ -> false
  in
  let pairs =
    List.map
      (fun ((shadow_id, ty), arg) ->
        ((shadow_id, ty), tail_shadow_arg ~shadow_ids ty arg))
      (* Same arity caveat as {!filter_by_mask}: a self-call of a different
         arity than the definition has no shadow-parameter correspondence, so
         decline rather than fail the extraction. *)
      ( if List.compare_lengths shadow_params args <> 0 then
          raise
            (Not_linearisable
               (Printf.sprintf
                  "a recursive call updates %d shadow parameter%s from %d \
                   argument%s"
                  (List.length shadow_params)
                  (if List.length shadow_params = 1 then "" else "s")
                  (List.length args)
                  (if List.length args = 1 then "" else "s") ))
        else List.combine shadow_params args )
  in
  (* Identify which params actually change (filter self-assignments). *)
  let non_trivial =
    List.filter
      (fun ((shadow_id, _ty), arg) -> not (is_self_assign shadow_id arg))
      pairs
  in
  (* Assigning an *owning* value-type shadow from a dereference is a
     self-destruction hazard: the pointee is very often a cell owned by that
     same shadow (walking a list tail via [_loop_l = *a1]).  [operator=] on the
     underlying [std::variant] is destroy-then-construct across alternatives, so
     it runs the old node's destructor -- dropping the last reference to the
     cell it is about to read -- and then constructs from freed storage.

     Materialising the source into a temporary first fixes this: the temporary
     is fully constructed before [operator=] is entered, so the source cell is
     still alive (and now also owned by the temporary) when the destination is
     torn down.  The cost is one shallow node copy, which the direct
     copy-assignment was paying anyway. *)
  let make_rhs ty arg =
    let core = match arg with CPPmove a -> a | a -> a in
    (* The shadow's declared type still carries the parameter's [const &]; the
       shadow itself is an owning value of the stripped type. *)
    let vty = strip_ref_and_const_type ty in
    match (ty, core) with
    | Tptr _, _ -> arg
    | _, CPPderef _ when is_value_type_ret vty ->
      Cpp_erasure.converting_ctor vty [core]
    | _ -> arg
  in
  if List.length non_trivial <= 1 then
    (* 0 or 1 assignment — no hazard possible, assign directly *)
    List.filter_map
      (fun ((shadow_id, ty), arg) ->
        if is_self_assign shadow_id arg then None
        else Some (Sasgn (shadow_id, Existing, make_rhs ty arg)) )
      pairs
  else (* 2+ assignments — use temporaries only where needed *)
    (* Check if expression [e] references variable [id]. *)
    let rec expr_mentions id e =
      match e with
      | CPPvar v -> Id.equal v id
      | _ ->
        let found = ref false in
        iter_expr_children
          ~on_expr:(fun e' -> if expr_mentions id e' then found := true)
          ~on_stmts:(fun _ -> ())
          e;
        !found
    in
    (* A variable needs a temporary iff some OTHER non-trivial assignment reads
       it in its RHS. *)
    let needs_temp shadow_id =
      List.exists
        (fun ((other_id, _), arg) ->
          not (Id.equal other_id shadow_id)
          && expr_mentions shadow_id arg)
        non_trivial
    in
    let temp_name (id : Id.t) : Id.t =
      let s = Id.to_string id in
      let base =
        if String.length s > 6 && String.sub s 0 6 = "_loop_" then
          String.sub s 6 (String.length s - 6)
        else if String.length s > 5 && String.sub s 0 5 = "_loop" then
          String.sub s 5 (String.length s - 5)
        else
          s
      in
      (* Avoid double underscores (reserved in C++) *)
      if String.length base > 0 && base.[0] = '_' then
        Id.of_string ("_next" ^ base)
      else
        Id.of_string ("_next_" ^ base)
    in
    (* Phase 1: emit temp declarations for hazardous variables, and direct
       assignments for non-hazardous ones. *)
    let temp_decls =
      List.filter_map
        (fun ((shadow_id, ty), arg) ->
          if needs_temp shadow_id then
            Some
              (Sasgn
                 ( temp_name shadow_id,
                   Declare (strip_ref_and_const_type ty),
                   make_rhs ty arg ))
          else
            None)
        non_trivial
    in
    let direct_assigns =
      List.filter_map
        (fun ((shadow_id, ty), arg) ->
          if needs_temp shadow_id then
            None
          else
            Some (Sasgn (shadow_id, Existing, make_rhs ty arg)))
        non_trivial
    in
    (* Phase 2: copy from temps back to loop variables. *)
    let temp_updates =
      List.filter_map
        (fun ((shadow_id, ty), _arg) ->
          if needs_temp shadow_id then
            let rhs =
              let stripped = strip_ref_and_const_type ty in
              if is_trivially_copyable_type stripped then
                CPPvar (temp_name shadow_id)
              else
                CPPmove (CPPvar (temp_name shadow_id))
            in
            Some (Sexpr (CPPbinop (Bassign, CPPvar shadow_id, rhs)))
          else
            None)
        non_trivial
    in
    temp_decls @ direct_assigns @ temp_updates

(** {2 Generic return-statement rewriter}

    The tail-recursion and TMC loopification passes share the same structural
    traversal of [Sif], [Scustom_case], [Smatch] and [Sblock].  They differ
    only in how they handle [Sreturn]:
    tail recursion assigns [_result] and breaks, while TMC patches a write
    pointer or allocates cells with holes.

    We factor out the shared traversal into a generic rewriter --
    {!generic_rewrite_stmt}/{!generic_rewrite_stmts} -- parameterised by a
    {!top_rewrite_config} record that captures the behavioural differences. *)

(** What the tail and TMC rewrites share: how recursive calls are recognised
    and which parameters vary. *)
type loop_rewrite_config = {
  rc_check : call_checker;
  (** Identifies recursive calls.  Returns [Some call_site] for a direct
      tail call, [None] otherwise. *)

  rc_varying : bool list;
  (** Mask parallel to function parameters: [true] = varying (needs a shadow
      variable), [false] = invariant (referenced directly). *)

  rc_shadow_params : (Id.t * cpp_type) list;
  (** Shadow variable bindings [(name, type)] for varying parameters.
      Used by {!make_shadow_updates} when rewriting tail calls. *)
}

(** Top-level rewrite configuration.  Combines a {!loop_rewrite_config}
    (used for match-branch bodies) with top-level-specific behaviour. *)
type top_rewrite_config = {
  trc_inner : loop_rewrite_config;
  (** Inner config for rewriting match-branch bodies. *)

  trc_tail_suffix : cpp_stmt list;
  (** Statements appended after tail-call shadow updates at the top level.
      Empty [[]] for plain tail recursion (control falls through to the
      [while (true)] test); [[Scontinue]] for TMC. *)

  trc_on_other : cpp_expr -> cpp_stmt;
  (** Emit code for a non-tail, non-visit return at the top level.
      Wraps in [Sblock] as needed. *)

  trc_rewrite_branch : smatch_branch -> smatch_branch;
  (** Transform a match branch at the top level. *)

  trc_detect_void_tail : bool;
  (** Whether to detect the void tail-call pattern
      [Sexpr call; Sreturn _] at the list level and rewrite it as
      [Sreturn (Some call)].  Enabled for plain tail recursion; disabled
      for TMC. *)
}

(** Generic top-level statement rewriter.

    Similar to {!generic_rewrite_lambda_return} but operates at the
    top level of the loop body rather than inside visitor lambdas:
    - Returns a single [cpp_stmt] (wrapping in [Sblock] as needed).
    - Handles [Sswitch] (only present at the top level of visitor bodies).
    - Uses {!generic_rewrite_stmts} for list-level recursion, which
      optionally detects the void tail-call pattern. *)
let rec generic_rewrite_stmt trc = function
  | Sreturn (Some e) ->
    ( match trc.trc_inner.rc_check e with
    | Some cs ->
      Sblock
        (make_shadow_updates trc.trc_inner.rc_shadow_params
           (filter_by_mask trc.trc_inner.rc_varying cs.cs_args)
         @ trc.trc_tail_suffix)
    | None -> trc.trc_on_other e )
  | Sif (cond, then_br, else_br) ->
    let rw = generic_rewrite_stmts trc in
    Sif (cond, rw then_br, rw else_br)
  | Sswitch (scrut, r, branches, default) ->
    let rw = generic_rewrite_stmts trc in
    Sswitch
      (scrut, r, List.map (fun (id, body) -> (id, rw body)) branches, default)
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    let rw = generic_rewrite_stmts trc in
    Scustom_case (ty, scrut, tyargs,
      List.map (fun (ps, ret_ty, body) -> (ps, ret_ty, rw body))
        branches, err)
  | Smatch (scrut, branches, default) ->
    let rw = generic_rewrite_stmts trc in
    Smatch (
      scrut,
      List.map
        (fun br ->
          let br' = trc.trc_rewrite_branch br in
          { br' with smb_body = rw br'.smb_body })
        branches,
      Option.map rw default)
  | Sblock stmts ->
    Sblock (generic_rewrite_stmts trc stmts)
  | s -> s

(** List-level top-level rewriter.

    Optionally detects the void tail-call pattern [Sexpr call; Sreturn _]:
    {v  call(); return;       (* void tail call *)
    call(); return val;   (* ITree unit-continuation variant *)  v}

    Both forms are rewritten as [Sreturn (Some call)] so the statement-level
    rewriter can handle them as ordinary tail calls.  This pattern is produced
    by [cofix_wrap] and [gen_stmts] for void-returning recursive functions. *)
and generic_rewrite_stmts trc = function
  | Sexpr e :: Sreturn _ :: rest
    when trc.trc_detect_void_tail && trc.trc_inner.rc_check e <> None ->
    generic_rewrite_stmt trc (Sreturn (Some e))
    :: generic_rewrite_stmts trc rest
  | s :: rest ->
    generic_rewrite_stmt trc s :: generic_rewrite_stmts trc rest
  | [] -> []

(** Wrap a statement list as a single statement. *)
let wrap_as_block = function
  | [s] -> s
  | ss -> Sblock ss

(** Rewrite a statement list for plain tail-call loopification.

    Constructs a tail-recursion {!top_rewrite_config} and delegates to
    {!generic_rewrite_stmts}.  Base returns assign [_result] and break;
    tail calls update shadow variables with no suffix (control falls through
    to the [while (true)] test).  Void tail-call detection is enabled. *)
let rewrite_visit_stmts check varying shadow_params =
  let inner_rc =
    { rc_check = check;
      rc_varying = varying;
      rc_shadow_params = shadow_params }
  in
  generic_rewrite_stmts
    { trc_inner = inner_rc;
      trc_tail_suffix = [];
      trc_on_other = (fun e -> wrap_as_block (assign_result_and_stop e));
      trc_rewrite_branch = Fun.id;
      trc_detect_void_tail = true }

(** Returns true if the statement declares a new variable or type binding. *)
let declares_variable = function
  | Sdecl _ | Sdecl_init _ | Sbind _ | Sstruct_def _ | Susing _ -> true
  | Sasgn (_, Declare _, _) -> true (* typed assignment = declaration *)
  | _ -> false

(** Names declared directly by a statement (not recursing into sub-statements). *)
let direct_decl_ids = function
  | Sdecl (id, _) | Sdecl_init (id, _) -> [ id ]
  | Sasgn (id, Declare _, _) -> [ id ]
  | Susing (id, _) -> [ id ]
  | Sbind (ids, _) -> ids
  | _ -> []

(** Returns true if inlining [block_stmts] before [rest] at the same scope level
    would produce a duplicate declaration.  A conflict arises when a name first
    declared inside [block_stmts] also appears as a top-level declaration in
    [rest] (including inside [Sblock] nodes in [rest] that would themselves be
    inlined). *)
let would_conflict block_stmts rest =
  if not (List.exists declares_variable block_stmts) then false
  else
    let block_ids = List.concat_map direct_decl_ids block_stmts in
    let rest_ids =
      List.concat_map
        (function
          | Sblock ss -> List.concat_map direct_decl_ids ss
          | s -> direct_decl_ids s)
        rest
    in
    List.exists (fun id -> List.mem id rest_ids) block_ids

(** Remove unnecessary [Sblock] wrappers throughout a statement list.

    An [Sblock] wrapper is unnecessary — and can be inlined into the surrounding
    list — when doing so would not introduce a duplicate declaration at the
    enclosing scope level.  Concretely:

    - [Sblock []] is always dropped.
    - [Sblock stmts] is inlined when none of its declared names would clash with
      a name declared by any sibling statement in the enclosing list.  Since each
      [if]/[else]/[while] branch already provides its own [{}] scope in the emitted
      C++, inner blocks inside those branches are almost always safe to remove.

    Recurses into [Sif], [Sswitch], [Scustom_case], [Smatch], and [Swhile] so
    that blocks nested inside branches are also simplified. *)
let rec strip_unnecessary_blocks = function
  | Sblock stmts :: rest ->
    let inner' = strip_unnecessary_blocks stmts in
    let rest' = strip_unnecessary_blocks rest in
    ( match inner' with
    | [] -> rest'
    | _ when not (would_conflict inner' rest') -> inner' @ rest'
    | _ -> Sblock inner' :: rest' )
  | s :: rest -> strip_loopify_stmt s :: strip_unnecessary_blocks rest
  | [] -> []

(** Recursively strip unnecessary blocks from a single statement's sub-branches
    ([Sif], [Sswitch], [Scustom_case], [Smatch], [Swhile], nested [Sblock]). *)
and strip_loopify_stmt = function
  | Sif (cond, then_br, else_br) ->
    Sif
      ( cond,
        strip_unnecessary_blocks then_br,
        strip_unnecessary_blocks else_br )
  | Sswitch (scrut, r, branches, default) ->
    Sswitch
      ( scrut,
        r,
        List.map (fun (id, body) -> (id, strip_unnecessary_blocks body)) branches,
        Option.map strip_unnecessary_blocks default )
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    Scustom_case
      ( ty,
        scrut,
        tyargs,
        List.map
          (fun (ps, ret_ty, body) -> (ps, ret_ty, strip_unnecessary_blocks body))
          branches,
        err )
  | Smatch (scrut, branches, default) ->
    Smatch
      ( scrut,
        List.map
          (fun br -> { br with smb_body = strip_unnecessary_blocks br.smb_body })
          branches,
        Option.map strip_unnecessary_blocks default )
  | Swhile (cond, body) -> Swhile (cond, strip_unnecessary_blocks body)
  | Sblock stmts ->
    (* Reached when an Sblock appears as a non-first element inside another
       statement (rare; the list-level case above handles the common path). *)
    let stmts' = strip_unnecessary_blocks stmts in
    ( match stmts' with
    | [] -> Sblock []
    | [ s ] -> s
    | _ -> Sblock stmts' )
  | s -> s

(** {3 Shadow variable setup}

    Both {!transform_tail} and {!transform_tmc} begin with an identical preamble:
    determine which parameters vary across recursive calls, compute pointer-safety
    flags, derive shadow variable names and types, and build the substitution map.
    This shared preamble is factored into {!build_shadow_setup}. *)

(** Result of the shared shadow-variable preamble for tail and TMC transforms.

    Every field is purely derived from the function's parameters, its body, and
    the call checker — no mutation, no side effects.  The record is consumed
    immediately by the caller to build shadow declarations and substitute
    parameter references. *)
type shadow_setup = {
  ss_varying : bool list;
      (** Bitmask parallel to [params]: [true] when the parameter changes
          across recursive calls and needs a shadow variable. *)
  ss_varying_params : (Id.t * cpp_type) list;
      (** Only the varying parameters (filtered by {!ss_varying}). *)
  ss_shadow_params : (Id.t * cpp_type) list;
      (** Shadow variable names ([_loop_X]) and types for each varying
          parameter, respecting pointer-safety (borrowed params become
          [const T*] shadows). *)
  ss_subs : (Id.t * Id.t) list;
      (** Substitution list: [(original_id, shadow_id)] pairs.  Applied to
          the function body via {!subst_stmt} so that references to the
          original parameter are redirected to the shadow variable. *)
}

(** Compute the shadow-variable setup shared by {!transform_tail} and
    {!transform_tmc}.

    Analyses the function body to determine which parameters vary across
    recursive calls, computes pointer-safety flags (whether a parameter can
    be borrowed as [const T*] instead of copied), derives shadow variable
    names ([_loop_X]) and types, and builds the old→new substitution list.

    @param check  Call checker identifying recursive calls
    @param params Function parameters [(id, type)]
    @param body   Function body statements
    @return {!shadow_setup} record consumed by the caller *)

(** Insert [std::move] at last-use positions of owned variables in loopified
    statement blocks.  Complements {!optimize_frame_push_args} which handles
    frame-push groups; this pass handles ordinary statements such as
    [_result = f(_result, _f.field)] and [_loop_x = g(a, _loop_x)].

    [self_ref_candidate key] — true when [key] should be moved in
    self-referencing assignments ([x = f(...x...)]).  Safe for loop
    accumulators whose liveness the caller knows ends with the overwrite.

    [last_use_candidate key] — true when [key] may be moved at its final
    read in the block.  Safe for [_result] and [_f.field] in single-shot
    handler bodies, NOT safe for loop variables (live across the back-edge). *)
let optimize_last_use_moves ~self_ref_candidate ~last_use_candidate stmts =
  let collect_reads expr =
    let tbl : (string, int) Hashtbl.t = Hashtbl.create 4 in
    let add key =
      let n = try Hashtbl.find tbl key with Not_found -> 0 in
      Hashtbl.replace tbl key (n + 1)
    in
    let rec walk = function
      | CPPmove _ | CPPlambda _ -> ()
      | CPPvar id -> add (Id.to_string id)
      | CPPaccess (Adot, CPPvar fid, field) when Id.equal fid id_f ->
        add (frame_field_key field)
      | e -> iter_expr_children ~on_expr:walk ~on_stmts:(fun _ -> ()) e
    in
    walk expr;
    tbl
  in
  let merge t1 t2 =
    Hashtbl.iter (fun k v ->
      let prev = try Hashtbl.find t1 k with Not_found -> 0 in
      Hashtbl.replace t1 k (prev + v)) t2;
    t1
  in
  let rec collect_reads_stmt stmt =
    match stmt with
    | Sexpr (CPPbinop (Bassign, CPPvar _, rhs)) -> collect_reads rhs
    | Sasgn (_, _, rhs) -> collect_reads rhs
    | Sexpr e -> collect_reads e
    | Sreturn (Some e) -> collect_reads e
    | s ->
      (* Recurse through nested statement lists — both arms of an [Sif], the
         [Smatch]/[Sswitch] branch bodies, [Sblock]/[Swhile] bodies — so a
         read in a *later* sibling branch is visible to [read_after].  A
         condition-only walk (the previous [Sif (cond, _, _)] arm) missed
         those reads and could [std::move] a value still read in a following
         branch. *)
      let tbl = Hashtbl.create 4 in
      iter_stmt_children
        ~on_expr:(fun e -> ignore (merge tbl (collect_reads e)))
        ~on_stmts:(fun stmts ->
          List.iter (fun s -> ignore (merge tbl (collect_reads_stmt s))) stmts)
        s;
      tbl
  in
  let rewrite_expr to_move expr =
    let rec rw = function
      | CPPmove _ as e -> e
      | CPPlambda _ as e -> e
      | CPPvar id as e ->
        if Hashtbl.mem to_move (Id.to_string id) then CPPmove e else e
      | CPPaccess (Adot, CPPvar fid, field) as e
        when Id.equal fid id_f ->
        let key = frame_field_key field in
        if Hashtbl.mem to_move key then CPPmove e else e
      | e -> map_expr rw Fun.id Fun.id e
    in
    rw expr
  in
  let rewrite_stmt to_move stmt =
    match stmt with
    | Sexpr (CPPbinop (Bassign, (CPPvar _ as lhs), rhs)) ->
      Sexpr (CPPbinop (Bassign, lhs, rewrite_expr to_move rhs))
    | _ ->
      map_stmt (rewrite_expr to_move) Fun.id Fun.id stmt
  in
  let build_to_move reads read_after stmt =
    let to_move : (string, unit) Hashtbl.t = Hashtbl.create 4 in
    ( match stmt with
      | Sexpr (CPPbinop (Bassign, CPPvar lhs, _))
      | Sasgn (lhs, _, _) ->
        let key = Id.to_string lhs in
        if self_ref_candidate key
           && (try Hashtbl.find reads key with Not_found -> 0) = 1
        then Hashtbl.replace to_move key ()
      | _ -> () );
    Hashtbl.iter (fun key count ->
      if last_use_candidate key
         && count = 1
         && not (Hashtbl.mem read_after key)
      then Hashtbl.replace to_move key ()
    ) reads;
    to_move
  in
  let rec process stmts =
    let stmts = List.map descend stmts in
    let n = List.length stmts in
    if n = 0 then []
    else
    let arr = Array.of_list stmts in
    let read_after = Array.init n (fun _ -> Hashtbl.create 4) in
    let running : (string, unit) Hashtbl.t = Hashtbl.create 8 in
    for i = n - 1 downto 0 do
      read_after.(i) <- Hashtbl.copy running;
      Hashtbl.iter (fun k _ -> Hashtbl.replace running k ())
        (collect_reads_stmt arr.(i))
    done;
    Array.to_list (Array.mapi (fun i s ->
      let reads = collect_reads_stmt s in
      let to_move = build_to_move reads read_after.(i) s in
      if Hashtbl.length to_move = 0 then s
      else rewrite_stmt to_move s
    ) arr)
  and descend stmt =
    match stmt with
    | Sif (cond, then_, else_) ->
      Sif (cond, process then_, process else_)
    | Smatch (scrut, branches, default) ->
      Smatch (
        scrut,
        List.map (fun br -> { br with smb_body = process br.smb_body }) branches,
        Option.map process default)
    | Sblock body -> Sblock (process body)
    | Swhile (cond, body) -> Swhile (cond, process body)
    | s -> s
  in
  process stmts

let build_shadow_setup tparams check params body =
  let varying = find_varying_params check params body in
  let pointer_safe = tail_pointer_safe_flags check params body () in
  let varying_params = filter_by_mask varying params in
  let varying_pointer_safe = filter_by_mask varying pointer_safe in
  let shadow_params =
    List.map2
      (fun (id, ty) safe ->
        (shadow_name id, tail_shadow_type ~tparams ~pointer_safe:safe ty))
      varying_params varying_pointer_safe
  in
  let subs =
    List.map2 (fun (id, _) (sid, _) -> (id, sid)) varying_params shadow_params
  in
  { ss_varying = varying; ss_varying_params = varying_params;
    ss_shadow_params = shadow_params; ss_subs = subs }

(** Drop the shadow variables a loop body only ever writes.

    A parameter can vary across recursive calls and still never be read — an
    index carried along only to keep a dependent type well-formed, say.  Its
    shadow is then set but never used, which [-Werror] rejects.  Remove both
    the declaration and the writes, iterating so that a staging temporary
    ([_next_x]) left dead by the removal goes too.

    @return the surviving declarations and the rewritten body *)
let drop_unread_shadows shadow_decls body =
  let declared_id = function
    | Sasgn (id, _, _) -> Some id
    | _ -> None
  in
  let write_target = function
    | Sasgn (id, _, _) | Sexpr (CPPbinop (Bassign, CPPvar id, _)) -> Some id
    | _ -> None
  in
  (* Every variable the statements *read* — the target of an assignment is a
     write, so only right-hand sides are walked. *)
  let reads stmts =
    let tbl = Hashtbl.create 16 in
    let rec walk_expr e =
      match e with
      | CPPvar id -> Hashtbl.replace tbl (Id.to_string id) ()
      | _ -> iter_expr_children ~on_expr:walk_expr ~on_stmts:walk_stmts e
    and walk_stmt s =
      match s with
      | Sasgn (_, _, rhs) | Sexpr (CPPbinop (Bassign, CPPvar _, rhs)) ->
        walk_expr rhs
      | _ -> iter_stmt_children ~on_expr:walk_expr ~on_stmts:walk_stmts s
    and walk_stmts ss = List.iter walk_stmt ss in
    walk_stmts stmts;
    tbl
  in
  (* Only loopification's own variables are candidates: a shadow, or the
     staging temporary that feeds one. *)
  let is_candidate decls id =
    List.exists (fun d -> declared_id d = Some id) decls
    || String.starts_with ~prefix:"_next_" (Id.to_string id)
  in
  let rec fixpoint decls body =
    let r = reads (decls @ body) in
    let dead id =
      is_candidate decls id && not (Hashtbl.mem r (Id.to_string id))
    in
    let live s = match write_target s with Some id -> not (dead id) | None -> true in
    (* A dead write nested in a branch becomes an empty block, which the
       existing cleanup pass then removes. *)
    let rec drop s =
      if live s then map_stmt Fun.id drop Fun.id s else Sblock []
    in
    let decls' = List.filter live decls in
    let body' = List.map drop body in
    if List.length decls' = List.length decls && body' = body then (decls, body)
    else fixpoint decls' body'
  in
  fixpoint shadow_decls body

(** Transform a tail-recursive function body into a [while] loop with shadow variables.

    Tail recursion is the simplest loopification case.  Since no work happens
    after the recursive call, we can convert it directly into iteration.

    {b Non-void functions} use a [_continue] guard variable and a [_result]
    accumulator:

    {v
    let rec f x = if base(x) then result else f(next(x))
    →
    T _result;
    auto _loop_x = x;
    bool _continue = true;
    while (_continue) {
      if (base(_loop_x)) { _result = result; _continue = false; }
      else { _loop_x = next(_loop_x); }
    }
    return _result;
    v}

    {b Void functions} (e.g. cofixpoint [spin], [forever]) never set
    [_continue = false] — their base cases exit via [return;] (which becomes
    [Sreturn None]) rather than assigning a result.  So [_continue] and
    [_result] are unnecessary and the loop simplifies to [while (true)]:

    {v
    CoFixpoint forever n := Tau (forever (S n))
    →
    auto _loop_n = n;
    while (true) { _loop_n = _loop_n + 1; }
    return;
    v}

    After rewriting, {!strip_empty_blocks} removes any empty [Sblock]s left
    by tail-call rewrites that produced no shadow updates (e.g. a
    zero-parameter cofixpoint like [spin] whose only recursive call has no
    arguments to update).

    @param param_inits Optional custom initializers for shadow variables
                       (default: copy from original parameter)
    @param check Call checker for identifying recursive calls
    @param params Function parameters [(id, type)] list
    @param ret_ty Return type of the function
    @param body Function body statements
    @return Transformed body with while loop structure *)
let transform_tail ?(param_inits = []) tparams check params ret_ty body =
  let { ss_varying = varying; ss_varying_params = varying_params;
        ss_shadow_params = shadow_params; ss_subs = subs } =
    build_shadow_setup tparams check params body
  in
  let is_void = ret_ty = Tvoid in
  (* Shadow variable declarations (only for varying params) *)
  let shadow_decls =
    List.map2
      (fun (orig_id, ty) (shadow_id, shadow_ty) ->
        let init_expr =
          match List.assoc_opt orig_id param_inits with
          | Some custom -> custom
          | None -> tail_shadow_init orig_id shadow_ty ty
        in
        Sasgn
          ( shadow_id,
            Declare (strip_ref_and_const_type shadow_ty),
            init_expr ) )
      varying_params
      shadow_params
  in
  (* Substitute param references in body *)
  let body' =
    List.map (subst_stmt subs) body
    |> rewrite_borrowed_shadow_uses shadow_params
  in
  (* Rewrite recursive calls (list-level rewrite handles void tail-call
     pattern [Sexpr call; Sreturn None] → [Sreturn (Some call)]) *)
  let body'' =
    rewrite_visit_stmts check varying shadow_params body'
  in
  let body'' = strip_unnecessary_blocks body'' in
  (* Move loop accumulators at self-referencing assignment sites:
     [_loop_x = f(_loop_x)] → [_loop_x = f(std::move(_loop_x))].
     General last-use is disabled for loop vars (live across the back-edge). *)
  let is_loop_cand key =
    List.exists (fun (id, ty) ->
      Id.to_string id = key
      && worthwhile_move_type (strip_ref_and_const_type ty))
    shadow_params
  in
  let body'' =
    optimize_last_use_moves
      ~self_ref_candidate:is_loop_cand
      ~last_use_candidate:(fun _ -> false)
      body''
  in
  (* Assemble the loop body.
     - Non-void: [... while (true) { ... return val; }]
     - Void:     [... while (true) { ... } return;]
     Non-void base cases return directly via [Sreturn] (from
     [assign_result_and_stop]); no [_result] variable or trailing return needed
     since [while (true)] without [break] never falls through.
     Void base cases exit via [Sreturn None] (plain [return;]).
     Both use [while (true)] for the loop condition. *)
  let shadow_decls, body'' = drop_unread_shadows shadow_decls body'' in
  let body'' = strip_unnecessary_blocks body'' in
  shadow_decls
  @ [Swhile (CPPbool true, body'')]
  @ (if is_void then [Sreturn None] else [])

(* {2 Non-tail recursion transformation}

   Non-tail recursion uses a frame-based stack with [_Enter] and continuation
   variants and a dispatch loop; see {!transform_nontail}. *)

