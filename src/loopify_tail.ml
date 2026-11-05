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

(** Create a shadow variable name for tail-recursion loop variables:
    [_loop_x], or [_loop_self] for [_self]. *)
let shadow_name (id : Id.t) : Id.t = Generated_name.prefixed "_loop" id

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

(** Return [true] when a parameter is worth moving into a shadow variable.
    References cannot be moved from; const values would trigger a
    pessimizing-move warning since the move constructor receives [const T&&]
    and falls back to copy anyway; and a move of a type that copies for free
    -- a scalar -- transfers nothing.  An [auto] parameter may be anything,
    and is moved as a type variable is ({!Ownership_plan.worth_moving}). *)
let is_moveable_param_type = function
  | Tref _ | Tconst _ -> false
  | Tauto -> true
  | ty -> worthwhile_move_type ty

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
    is decided separately by {!pointer_safe_flags}: an accumulator that is
    rebuilt each iteration ([acc := Cons(x, acc)]) is not pointer-safe and keeps
    its value shadow.

    A [const T] parameter qualifies for the same reason, under any policy: it
    lives for the whole call, and being const nothing moves out of it.  A
    helper lifted out of a definition for a polymorphic local fixpoint
    declares its parameters so.

    @return [Some pointee_type] when the parameter qualifies, [None] otherwise *)
let borrowed_value_param_pointee = function
  | Tref (Lvalue, Tconst t) when is_value_type_ret t -> Some t
  | Tconst (Tref (Lvalue, t)) when is_value_type_ret t -> Some t
  | Tconst t when is_value_type_ret t -> Some t
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

(** The variable whose storage [e] stays inside, through dereferences, moves,
    member accesses and variant projections ([x.v()], [std::get<K>(e)]): one
    [root] accepts, or the one a binder [bound] maps to. *)
let rec storage_root ~root ~bound e =
  let inside = storage_root ~root ~bound in
  match e with
  | CPPvar x -> if root x then Some x else bound x
  | CPPderef e | CPPmove e | CPPaccess (Adot, e, _) | CPPaccess (Aarrow, e, _)
  | CPPget (e, _) | CPPget' (e, _, _) | CPPunop (_, e) ->
    inside e
  | CPPfun_call (_, CPPrt Crane_rt.Raw, {rev = [e]}) -> inside e
  | CPPfun_call (_, CPPaccess (Adot, e, _), {rev = []}) | CPPaccess_call (Aarrow, e, _, []) ->
    inside e
  | CPPstd_get (_, Some e) -> inside e
  | _ -> None

(** Pointer-safety flags for [params]: those of them every recursive call
    passes a value stored in what the caller passed for it, as the loop's
    ControlIR says ({!Control_ir.parts_passed}), [parts], that are a
    borrowed value type. *)
let pointer_safe_flags ~parts params =
  List.map2 (fun part (_, ty) -> part && Option.has_some (borrowed_value_param_pointee ty)) parts params

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
      (* A scrutinee whose object is a pointer shadow -- [xs.v()] -- is
         matched through it, as a pointer rather than a value.  One whose
         object only mentions a shadow -- a call taking it as an argument --
         is a value like any other, the shadow read in it dereferenced. *)
      let ptr_scrutinee =
        match scrut.sc_expr with
        | CPPvar id
        | CPPaccess_call (_, CPPvar id, _, [])
        | CPPfun_call (_, CPPaccess (_, CPPvar id, _), {rev = []}) ->
          is_ptr_shadow id
        | _ -> false
      in
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
    aliased by the caller.

    [aliases] are the binders that lie inside the storage of a shadow kept
    by value, each with its shadow: a structured binding of a match on
    [_loop_l.v()].  Reading one reads the shadow, so an update reading [a0]
    of [_loop_l] is evaluated before [_loop_l] is overwritten, which
    overwrites [a0] with the next cell's field.

    [derefs] are the variables declared as references to a dereference
    ([const T &a1_value = *a1]), each with the pointer it dereferences: one
    stands for that dereference.

    [owned] are the locals of the turn the jump ends held by value, worth
    moving and with no reference bound into them: one assigned whole to a
    shadow kept by value, or to a temporary, where the updates read it for
    the last time dies there, and is moved. *)
let make_shadow_updates ?(aliases = []) ?(derefs = []) ?(owned = []) shadow_params args =
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
      ( if List.compare_lengths shadow_params args <> 0 then
          arity_mismatch ~args:(List.length args) ~params:(List.length shadow_params)
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
    let dereference = function
      | CPPderef _ -> true
      | CPPvar v -> List.exists (fun (x, _) -> Id.equal v x) derefs
      | _ -> false
    in
    match (ty, core) with
    | Tptr _, _ -> arg
    | _, core when dereference core && is_value_type_ret vty ->
      Cpp_erasure.converting_ctor vty [core]
    | _ -> arg
  in
  (* An owned local assigned whole to a shadow kept by value at its last
     read among the updates dies there, and is moved. *)
  let rec pointer = function Tptr _ -> true | Tconst t | Tref (_, t) -> pointer t | _ -> false in
  let by_value id = List.exists (fun (s, ty) -> Id.equal s id && not (pointer ty)) shadow_params in
  let moved_at_last_read updates =
    fst
      (List.fold_right
         (fun s (after, read) ->
           let last v = List.exists (Id.equal v) owned && not (List.exists (Id.equal v) read) in
           let s =
             match s with
             | Sasgn (x, Existing, CPPvar v) when by_value x && last v -> Sasgn (x, Existing, CPPmove (CPPvar v))
             | Sasgn (x, (Declare (ty, _) as d), CPPvar v) when (not (pointer ty)) && last v ->
               Sasgn (x, d, CPPmove (CPPvar v))
             | s -> s
           in
           let reads = match s with Sasgn (_, _, e) | Sexpr e -> free_vars_expr e | _ -> [] in
           (s :: after, reads @ read) )
         updates ([], []))
  in
  moved_at_last_read @@
  if List.length non_trivial <= 1 then
    (* 0 or 1 assignment — no hazard possible, assign directly *)
    List.filter_map
      (fun ((shadow_id, ty), arg) ->
        if is_self_assign shadow_id arg then None
        else Some (Sasgn (shadow_id, Existing, make_rhs ty arg)) )
      pairs
  else (* 2+ assignments — use temporaries only where needed *)
    (* Whether [e] reads one of the variables [names]. *)
    let rec mentions names e =
      match e with
      | CPPvar v -> List.exists (Id.equal v) names
      | _ ->
        let found = ref false in
        iter_expr_children
          ~on_expr:(fun e' -> if mentions names e' then found := true)
          ~on_stmts:(fun _ -> ())
          e;
        !found
    in
    (* A variable needs a temporary iff some OTHER non-trivial assignment reads
       it in its RHS by name, or one made after it, not itself through a
       temporary, reads a binder inside it.  A right-hand side put in a
       temporary is evaluated before any variable is assigned, and one
       assigned before the variable reads what it still holds; the staged
       variables are therefore settled last first. *)
    let by_name ((shadow_id, _), _) =
      List.exists
        (fun ((other_id, _), arg) ->
          not (Id.equal other_id shadow_id)
          && mentions [shadow_id] arg)
        non_trivial
    in
    let inside shadow_id =
      List.filter_map (fun (b, s) -> if Id.equal s shadow_id then Some b else None) aliases
    in
    let staged =
      List.fold_right
        (fun (((shadow_id, _), _) as update) later ->
          let read_later =
            match inside shadow_id with
            | [] -> false
            | names -> List.exists (fun ((_, arg), staged) -> (not staged) && mentions names arg) later
          in
          (update, by_name update || read_later) :: later)
        non_trivial []
    in
    let needs_temp shadow_id =
      List.exists (fun (((id, _), _), staged) -> staged && Id.equal id shadow_id) staged
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
      Generated_name.prefixed "_next" (Id.of_string base)
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
                   Declare (strip_ref_and_const_type ty, None),
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
    (* Phase 2: copy from temps back to loop variables.  A temporary is dead
       once copied, so it is moved unless copying it is known to cost
       nothing: a trivially copyable type, but not a type parameter, which
       may stand for one worth moving. *)
    let temp_updates =
      List.filter_map
        (fun ((shadow_id, ty), _arg) ->
          if needs_temp shadow_id then
            let rhs =
              let stripped = strip_ref_and_const_type ty in
              if is_trivially_copyable_type stripped && not (worthwhile_move_type stripped) then
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

  rc_jumped : cpp_expr -> unit;
  (** Told each recursive call rewritten into a jump. *)
}

(** Top-level rewrite configuration.  Combines a {!loop_rewrite_config}
    (used for match-branch bodies) with top-level-specific behaviour. *)
type top_rewrite_config = {
  trc_inner : loop_rewrite_config;
  (** Inner config for rewriting match-branch bodies. *)

  trc_jump :
    derefs:(Id.t * cpp_expr) list -> updates:(cpp_expr list -> cpp_stmt list) -> cpp_expr -> cpp_expr list -> cpp_stmt list;
  (** The statements a recursive call [e] in tail position passing [args],
      every parameter's, becomes, under the references to a dereference
      [derefs] declared before it, where [updates args] are the shadow
      updates passing [args] ({!make_shadow_updates}).  Plain tail recursion
      falls through to the [while (true)] test after them; TMC continues. *)

  trc_on_other : derefs:(Id.t * cpp_expr) list -> cpp_expr -> cpp_stmt;
  (** Emit code for a non-tail, non-visit return at the top level, under
      the references to a dereference [derefs] declared before it
      ({!make_shadow_updates}).  Wraps in [Sblock] as needed. *)

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
let rec generic_rewrite_stmt ?(aliases = []) ?(derefs = []) ?(owned = []) trc = function
  | Sreturn (Some e) ->
    ( match trc.trc_inner.rc_check e with
    | Some cs ->
      trc.trc_inner.rc_jumped e;
      let updates args =
        make_shadow_updates ~aliases ~derefs ~owned trc.trc_inner.rc_shadow_params
          (filter_by_mask trc.trc_inner.rc_varying args)
      in
      Sblock (trc.trc_jump ~derefs ~updates e cs.cs_args)
    | None -> trc.trc_on_other ~derefs e )
  | Sif (cond, then_br, else_br) ->
    let rw = generic_rewrite_stmts ~aliases ~derefs ~owned trc in
    Sif (cond, rw then_br, rw else_br)
  | Sswitch (scrut, r, branches, default) ->
    let rw = generic_rewrite_stmts ~aliases ~derefs ~owned trc in
    Sswitch
      (scrut, r, List.map (fun (id, body) -> (id, rw body)) branches, default)
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    let rw = generic_rewrite_stmts ~aliases ~derefs ~owned trc in
    Scustom_case (ty, scrut, tyargs,
      List.map (fun (ps, ret_ty, body) -> (ps, ret_ty, rw body))
        branches, err)
  | Smatch (scrut, branches, default) ->
    (* A match on the storage of a shadow kept by value binds into it: its
       bindings are aliases of the shadow while the branch runs, and
       overwriting the shadow overwrites them.  A pointer shadow is only
       repointed; what it pointed at stays where it was. *)
    let rec pointer = function Tptr _ -> true | Tconst t | Tref (_, t) -> pointer t | _ -> false in
    let by_value =
      List.filter_map
        (fun (id, ty) -> if pointer ty then None else Some id)
        trc.trc_inner.rc_shadow_params
    in
    let root =
      storage_root
        ~root:(fun x -> List.exists (Id.equal x) by_value)
        ~bound:(fun x -> List.assoc_opt x aliases)
        scrut.sc_expr
    in
    let inside br =
      match root with
      | None -> aliases
      | Some s ->
        let bound = List.map (fun fb -> fb.fb_name) br.smb_field_bindings in
        let bound = match br.smb_var with Some v -> v :: bound | None -> bound in
        List.map (fun b -> (b, s)) bound @ aliases
    in
    (* A branch binds into its scrutinee, which it must not move. *)
    let branch_owned = List.filter (fun x -> not (List.exists (Id.equal x) (free_vars_expr scrut.sc_expr))) owned in
    Smatch (
      scrut,
      List.map
        (fun br ->
          let br' = trc.trc_rewrite_branch br in
          { br' with smb_body = generic_rewrite_stmts ~aliases:(inside br') ~derefs ~owned:branch_owned trc br'.smb_body })
        branches,
      Option.map (generic_rewrite_stmts ~aliases ~derefs ~owned trc) default)
  | Sblock stmts ->
    Sblock (generic_rewrite_stmts ~aliases ~derefs ~owned trc stmts)
  | s -> s

(** List-level top-level rewriter.

    Optionally detects the void tail-call pattern [Sexpr call; Sreturn _]:
    {v  call(); return;       (* void tail call *)
    call(); return val;   (* ITree unit-continuation variant *)  v}

    Both forms are rewritten as [Sreturn (Some call)] so the statement-level
    rewriter can handle them as ordinary tail calls.  This pattern is produced
    by [cofix_wrap] and [gen_stmts] for void-returning recursive functions. *)
and generic_rewrite_stmts ?(aliases = []) ?(derefs = []) ?(owned = []) trc = function
  | Sexpr e :: Sreturn _ :: rest
    when trc.trc_detect_void_tail && trc.trc_inner.rc_check e <> None ->
    generic_rewrite_stmt ~aliases ~derefs ~owned trc (Sreturn (Some e))
    :: generic_rewrite_stmts ~aliases ~derefs ~owned trc rest
  | s :: rest ->
    let s' = generic_rewrite_stmt ~aliases ~derefs ~owned trc s in
    let derefs =
      match s with
      | Sasgn (id, Declare (ty, _), CPPderef pointer) when is_reference_type ty -> (id, pointer) :: derefs
      | _ -> derefs
    in
    (* A local declared by value worth moving is owned; a reference is not,
       nor what one is bound into, nor what a closure made here captures,
       which a later update calling it reads. *)
    let disown ids = List.filter (fun x -> not (List.exists (Id.equal x) ids)) owned in
    let captured e = if expr_exists (function CPPlambda _ -> true | _ -> false) e then free_vars_expr e else [] in
    let owned =
      match s with
      | Sasgn (id, Declare (ty, _), e) when is_borrowed ty -> disown (id :: free_vars_expr e)
      | Sasgn (id, Declare (ty, _), e) ->
        let owned = disown (id :: captured e) in
        if movable ty then id :: owned else owned
      | Sasgn (_, _, e) | Sexpr e -> disown (captured e)
      | Sdecl (id, ty, _) -> if movable ty then id :: disown [id] else disown [id]
      | Sbind (ids, e) -> disown (ids @ free_vars_expr e)
      | _ -> owned
    in
    s' :: generic_rewrite_stmts ~aliases ~derefs ~owned trc rest
  | [] -> []

(** Wrap a statement list as a single statement. *)
let wrap_as_block = function
  | [s] -> s
  | ss -> Sblock ss

(** Rewrite a statement list for plain tail-call loopification.

    Constructs a tail-recursion {!top_rewrite_config} and delegates to
    {!generic_rewrite_stmts}.  Base returns assign [_result] and break;
    tail calls update shadow variables with no suffix (control falls through
    to the [while (true)] test).  Void tail-call detection is enabled.
    [jumped] is told each call rewritten into a jump. *)
let rewrite_visit_stmts ~jumped check varying shadow_params =
  let inner_rc =
    { rc_check = check;
      rc_varying = varying;
      rc_shadow_params = shadow_params;
      rc_jumped = jumped }
  in
  generic_rewrite_stmts
    { trc_inner = inner_rc;
      trc_jump = (fun ~derefs:_ ~updates _ args -> updates args);
      trc_on_other = (fun ~derefs:_ e -> wrap_as_block (assign_result_and_stop e));
      trc_rewrite_branch = Fun.id;
      trc_detect_void_tail = true }

(** Returns true if the statement declares a new variable or type binding. *)
let declares_variable = function
  | Sdecl _ | Sdecl_init _ | Sbind _ | Sstruct_def _ | Susing _ -> true
  | Sasgn (_, Declare _, _) -> true (* typed assignment = declaration *)
  | _ -> false

(** Names declared directly by a statement (not recursing into sub-statements). *)
let direct_decl_ids = function
  | Sdecl (id, _, _) | Sdecl_init (id, _) -> [ id ]
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

(** The jumps [check] finds, each moving into the next value of a shadow
    kept by value the shadow itself where the plan moves it there
    ({!Ownership_plan.continue_moves}): [moves] gives, by the occurrence of
    the call a jump is made of, a flag for each of [params], the shadows'
    names [subs] stand for.  The argument reads the shadow once, outside any
    closure and not already moved; reading it otherwise it is left, and
    where that is a spelling the plan's one read does not account for --
    no read, or two, or one in another argument -- reported under
    [CRANE_CHECK_IR]. *)
let moving_jumps ~moves ~subs ~shadow_params params (check : call_checker) : call_checker =
  if moves = [] then check
  else
    let rec pointer = function Tptr _ -> true | Tconst t | Tref (_, t) -> pointer t | _ -> false in
    let by_value shadow =
      match List.assoc_opt shadow shadow_params with Some ty -> not (pointer ty) | None -> false
    in
    let move_read x arg =
      let bare = ref 0 and moved = ref 0 and captured = ref 0 in
      let rec count = function
        | CPPmove (CPPvar y) -> if Id.equal x y then incr moved
        | CPPlambda _ as l -> if List.exists (Id.equal x) (free_vars_expr l) then incr captured
        | CPPmove _ -> ()
        | CPPvar y -> if Id.equal x y then incr bare
        | e -> iter_expr_children ~on_expr:count ~on_stmts:(fun _ -> ()) e
      in
      count arg;
      let rec move_in = function
        | (CPPmove _ | CPPlambda _) as e -> e
        | CPPvar y as e when Id.equal x y -> CPPmove e
        | e -> map_expr move_in Fun.id Fun.id e
      in
      if !bare = 1 then move_in arg
      else begin
        (* Translation moved it already, the parameter being owned there; or
           the read is inside a closure translation made around it -- a
           partial application eta-expanded -- whose capture takes it as
           the plan's captures say ({!Ownership_plan.moved_captures}). *)
        if not (!bare = 0 && !moved + !captured = 1) then
          Probe.violation "ownership plan"
            Pp.(str "a jump the plan moves " ++ Id.print x ++ str " into its next value at reads it " ++ int !bare ++ str " times");
        arg
      end
    in
    fun e ->
      match check e with
      | Some site -> (
        let flags =
          Option.bind (made_of e) (fun o ->
              List.find_map (fun (o', flags) -> if Miniml.Occurrence.equal o o' then Some flags else None) moves )
        in
        match flags with
        | Some flags when List.compare_lengths flags params = 0 && List.compare_lengths site.cs_args params = 0 ->
          (* Another argument spelling the shadow reads it where the plan's
             Core does not: it is left. *)
          let spelled_elsewhere k x =
            List.exists (fun (j, a) -> j <> k && List.exists (Id.equal x) (free_vars_expr a))
              (List.mapi (fun j a -> (j, a)) site.cs_args)
          in
          let args =
            List.mapi
              (fun k ((flag, (id, _)), arg) ->
                match List.assoc_opt id subs with
                | Some shadow when flag && by_value shadow ->
                  if spelled_elsewhere k shadow then begin
                    Probe.violation "ownership plan"
                      Pp.(str "a jump the plan moves " ++ Id.print shadow ++ str " into its next value at reads it in another argument");
                    arg
                  end
                  else move_read shadow arg
                | Some _ | None -> arg )
              (List.combine (List.combine flags params) site.cs_args)
          in
          Some {site with cs_args = args}
        | Some _ | None -> Some site )
      | None -> None

let build_shadow_setup ~varying ~parts tparams params =
  let pointer_safe = pointer_safe_flags ~parts params in
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
    @param jumped Told each recursive call rewritten into a jump
    @param varying Which parameters the recursive calls change, where the
                   caller knows; read off the calls [check] finds otherwise
    @param check Call checker for identifying recursive calls
    @param params Function parameters [(id, type)] list
    @param ret_ty Return type of the function
    @param body Function body statements
    @return Transformed body with while loop structure *)
let transform_tail ?(param_inits = []) ?(jumped = ignore) ?(moves = []) ~varying ~parts tparams check params ret_ty body =
  let { ss_varying = varying; ss_varying_params = varying_params;
        ss_shadow_params = shadow_params; ss_subs = subs } =
    build_shadow_setup ~varying ~parts tparams params
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
            Declare (strip_ref_and_const_type shadow_ty, None),
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
  let check = moving_jumps ~moves ~subs ~shadow_params params check in
  let body'' =
    rewrite_visit_stmts ~jumped check varying shadow_params body'
  in
  let body'' = strip_unnecessary_blocks body'' in
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

   Non-tail recursion uses a frame-based stack with [CraneEnter] and continuation
   variants and a dispatch loop; see {!transform_nontail}. *)

