(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Tail-recursion loopification for {!Loopify}: the [while] rewrite
    ({!transform_tail}), the generic return-statement rewriter that
    {!Loopify_tmc} shares, and the shadow variables every strategy declares
    for the parameters a loop varies ({!build_shadow_setup},
    {!make_shadow_updates}).  Runs on {!Cpp_ir.Lowered} function bodies, after
    translation and before printing; which functions it lowers, and which
    calls are its jumps, the ControlIR of each loop decides
    ({!Control_to_legacy_minicpp}). *)

open Names
open Cpp_ir.Type
open Cpp_ir.Stmt
open Cpp_ir.Expr
open Loopify_analysis

(** {2 Tail recursion transformation}

    The body runs inside [while (true)].  Each arm either returns its value
    directly, which leaves the loop and the function, or updates the shadow
    parameters and falls through to the next iteration.

    {[
      auto _loop_x = x; auto _loop_l = l;
      while (true) \{
        auto &&_sv = _loop_l->v();
        if (std::holds_alternative<Base>(_sv)) \{
          return base_val;
        \} else \{
          _loop_x = new_x; _loop_l = new_l;
        \}
      \}
    ]} *)

(** Create a shadow variable name for tail-recursion loop variables:
    [_loop_x], or [_loop_self] for [_self]. *)
let shadow_name (id : Id.t) : Id.t = Generated_name.prefixed "_loop" id

(** Strip reference and const modifiers from a type, converting it to a value
    type suitable for local variable declarations. [const shared_ptr<T> &]
    becomes [shared_ptr<T>], and [F0 &&] ([Reference (Forwarding, Variable)]) becomes [Variable].
*)
let rec strip_ref_type = function
  | Reference (_, t) -> strip_ref_type t
  | t -> t

(** Strip reference types AND const modifiers from a type. Used for shadow
    variables in tail recursion, which must be mutable to support reassignment
    in the loop body.  However, [const] on a pointer pointee is preserved:
    [const tree *] stays [const tree *] because the pointer variable itself is
    mutable (can be reassigned), while the [const] just prevents modification
    through the pointer; removing it would break [_loop_self = this] when
    [this] is [const T *] in a const method. *)
let rec strip_ref_and_const_type = function
  | Reference (_, t) -> strip_ref_and_const_type t
  | Const (Pointer _) as t -> t
  | Const t -> strip_ref_and_const_type t
  | t -> t

(** Return [true] when a parameter is worth moving into a shadow variable.
    References cannot be moved from; const values would trigger a
    pessimizing-move warning since the move constructor receives [const T&&]
    and falls back to copy anyway; and a move of a type that copies for free
    -- a scalar -- transfers nothing.  An [auto] parameter may be anything,
    and is moved as a type variable is ({!Ownership_ir.worth_moving_cpp}). *)
let is_moveable_param_type = function
  | Reference _ | Const _ -> false
  | Auto -> true
  | ty -> worthwhile_move_type ty

(** Extract the pointee type from a "borrowed value-type" parameter.

    A borrowed value-type parameter is one declared as [const T&] where [T] is a
    value-type inductive.  These can be optimised to [const T*] shadows that
    avoid copying the entire value at each loop iteration.

    Under [Crane Reuse] with non-atomic reference counts
    ({!Table.non_atomic_rc}) an owned by-value parameter qualifies too.  Reuse
    needs the scrutinee owned (that is what gives the loop cells it may
    recycle), and escape analysis ({!Escape}) therefore passes it by value;
    without this case the shadow
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
  | Reference (Lvalue, Const t) when is_value_type_ret t -> Some t
  | Const (Reference (Lvalue, t)) when is_value_type_ret t -> Some t
  | Const t when is_value_type_ret t -> Some t
  | t when Table.reuse () && Table.non_atomic_rc () && is_value_type_ret t ->
    Some t
  | _ -> None

(** Extract the underlying type variable id from a forwarding-reference type.
    [Reference (Forwarding, Variable (Index (_, Some id) | Named id))] gives
    [Some id]; any reference wrapper is looked through, not only a
    forwarding one. *)
let rec extract_fwd_ref_tvar = function
  | Reference (_, inner) -> extract_fwd_ref_tvar inner
  | Variable (Index (_, Some id) | Named id) -> Some id
  | _ -> None

(** The arrow a template parameter is constrained to, when it is a callable one.
    [tparams] holds [(kind, name)] pairs from the surrounding template header;
    a [Callable_declared (dom, cod)] kind is what becomes the
    [std::is_invocable_r_v<cod, F &, dom &...>] clause. *)
let lookup_tparam_fun_type tparams id =
  let name = Id.to_string id in
  List.find_map
    (fun ((tt : param_kind), tparam_id) ->
      match tt with
      | Callable_declared (dom, cod) when String.equal (Id.to_string tparam_id) name ->
        Some (Function (dom, cod))
      | _ -> None )
    tparams

(** Compute the shadow variable type for a tail-recursive loop.

    When [pointer_safe] is [true] and the parameter is a borrowed value-type
    ([const T&] where [T] is a value-type inductive), the shadow becomes
    [const T*] (raw pointer).

    A callable parameter arrives as a deduced template parameter (the caller's
    closure type), and a shadow exists only because the back edge reassigns it.
    Those two facts cannot both hold of one variable: a closure type has exactly
    one value, so nothing the loop builds is assignable to it.  The shadow has
    to be a type that can hold every callable the loop puts in it, which is the
    arrow the parameter's constraint already states.

    Otherwise the shadow inherits the parameter's type verbatim. *)
let tail_shadow_type ~tparams ~pointer_safe ty =
  match (pointer_safe, borrowed_value_param_pointee ty) with
  | true, Some t -> Pointer (Const t)
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
  | Pointer _, Some _ -> Unary (Address_of, Local orig_id)
  | _ ->
    if is_moveable_param_type ty then Move (Local orig_id)
    else Local orig_id

(** Adjust a recursive-call argument to match the shadow variable's type.

    - When the shadow is a pointer and the argument is [*shadow_var]
      (i.e., dereference of one of our own pointer-safe shadows): just use
      [shadow_var] directly since it is already a raw pointer.
    - When the shadow is a pointer and the argument is [*ptr]: use
      [crane_raw(ptr)] (works whether [ptr] is a smart pointer or already raw,
      as under [Crane Arena])
    - When the shadow is a pointer and the argument is a variable: [&arg]
    - Otherwise: pass through unchanged

    @param shadow_ids  Shadow variable IDs that are already raw pointers *)
let tail_shadow_arg ~shadow_ids shadow_ty arg =
  match shadow_ty, arg with
  | Pointer _, Dereference (Local id) when List.exists (Id.equal id) shadow_ids ->
    Local id
  | Pointer _, Dereference inner ->
    Call (call_opaque, Runtime Crane_rt.Raw, [inner])
  | Pointer _, Local _ -> Unary (Address_of, arg)
  | _ -> arg

(** The variable whose storage [e] stays inside, through dereferences, moves,
    member accesses and variant projections ([x.v()], [std::get<K>(e)]): one
    [root] accepts, or the one a binder [bound] maps to. *)
let rec storage_root ~root ~bound e =
  let inside = storage_root ~root ~bound in
  match e with
  | Local x -> if root x then Some x else bound x
  | Dereference e | Move e | Access (Dot, e, _) | Access (Arrow, e, _)
  | Member (e, _) | Project (e, _, _) | Unary (_, e) ->
    inside e
  | Call (_, Runtime Crane_rt.Raw, [e]) -> inside e
  | Call (_, Access (Dot, e, _), []) | Access_call (Arrow, e, _, []) ->
    inside e
  | Variant_get (_, Some e) -> inside e
  | _ -> None

(** Pointer-safety flags for [params], parallel to it: a parameter is
    pointer-safe when every recursive call passes it a value stored inside
    what the caller passed for it ([parts], as the loop's ControlIR derives
    it with {!Control_ir.Term.parts_passed}) and its type is a borrowed value
    type ({!borrowed_value_param_pointee}). *)
let pointer_safe_flags ~parts params =
  List.map2 (fun part (_, ty) -> part && Option.has_some (borrowed_value_param_pointee ty)) parts params

(** Rewrite references to pointer-safe shadow variables ([const T*]) so that
    reads dereference the pointer and method calls use [->] via
    [Access_call].

    Pointer-safe shadows store a [const T*] instead of copying the value.
    Code originally written against [const T&] needs adjustment:
    - Bare variable access [id] becomes [*id]
    - Member calls [id.method(args)] become [id->method(args)]
    - Direct assignments [id = rhs] keep the LHS undereferenced (the
      pointer itself is being reassigned)
    - A match whose scrutinee's object is a pointer shadow ([xs.v()]) is
      matched through [->]; any other scrutinee is rewritten as an
      ordinary expression

    @param shadow_params The shadow parameter list; only entries whose type
                         is [Pointer _] are considered pointer-safe
    @param stmts         Statement list to rewrite
    @return Rewritten statements with pointer dereferences inserted *)
let rewrite_borrowed_shadow_uses shadow_params stmts =
  let ptr_shadows =
    List.filter_map
      (fun (id, ty) -> match ty with Pointer _ -> Some id | _ -> None)
      shadow_params
  in
  let is_ptr_shadow id = List.exists (Id.equal id) ptr_shadows in
  let rec expr = function
    | Call (_, Access (Dot, Local id, meth), args)
      when is_ptr_shadow id ->
      Access_call (Arrow, Local id, meth, List.map expr args)
    | Local id when is_ptr_shadow id -> Dereference (Local id)
    | e -> map_expr expr stmt Fun.id e
  and stmt = function
    | Expression (Binary (Assign, Local id, rhs)) when is_ptr_shadow id ->
      (* Assignment to a pointer shadow: keep the LHS as a raw pointer
         (don't dereference it), only rewrite the RHS. *)
      Expression (Binary (Assign, Local id, expr rhs))
    | Match (scrut, branches, default) ->
      (* A scrutinee whose object is a pointer shadow -- [xs.v()] -- is
         matched through it, as a pointer rather than a value.  One whose
         object only mentions a shadow -- a call taking it as an argument --
         is a value like any other, the shadow read in it dereferenced. *)
      let ptr_scrutinee =
        match scrut.expr with
        | Local id
        | Access_call (_, Local id, _, [])
        | Call (_, Access (_, Local id, _), []) ->
          is_ptr_shadow id
        | _ -> false
      in
      Match
        ( { scrut with
            expr =
              (if ptr_scrutinee then scrut.expr else expr scrut.expr);
            access = (if ptr_scrutinee then Arrow else scrut.access) },
          List.map
            (fun (br : branch) ->
              { br with
                extra_conditions = List.map expr br.extra_conditions;
                body = List.map stmt br.body })
            branches,
          Option.map (List.map stmt) default )
    | s -> map_stmt expr stmt Fun.id s
  in
  List.map stmt stmts

(** Whether a shadow's C++ type is a pointer ([const T *]), seen through
    [const] and references: a pointer shadow is repointed, never
    overwritten in place. *)
let rec pointer = function Pointer _ -> true | Const t | Reference (_, t) -> pointer t | _ -> false

(** Wrap [e] in [std::move] only when it is an lvalue (a plain variable
    reference).  Wrapping rvalues (function calls, literals, binary ops) in
    [std::move] is a pessimising move: it prevents copy elision on the
    assignment and is rejected by [-Wpessimizing-move]. *)
let move_if_lvalue = function
  | Local _ as e -> Move e
  | e -> e

(** Assign [expr] to the [_result] accumulator variable:
    the statement list [[\[_result = expr;\]]].  Used by the frame machine
    ({!Loopify_frame}), which keeps a [_result]; the tail loop returns
    directly ({!return_result}). *)
let assign_result expr =
  [Expression (Binary (Assign, Local (id_result), move_if_lvalue expr))]

(** Return [expr] directly from the tail-recursion [while (true)] loop, which
    leaves both the loop and the function.  Used only in tail-recursion
    rewriting. *)
let return_result expr =
  [ Return (Some (move_if_lvalue expr)) ]

(** Generate temp-based parameter updates to avoid read-after-write hazards. For
    a recursive call like [f b (a mod b)], we must evaluate all argument
    expressions (which reference [_loop_] variables) before overwriting any of
    them. We emit [auto _next_a = expr_for_a; auto _next_b = expr_for_b;
    _loop_a = std::move(_next_a); _loop_b = std::move(_next_b);], staging
    through a temporary only the variables another update reads.

    Self-assignments ([_loop_x = _loop_x]) are skipped entirely. With at most
    one non-trivial assignment no temporary is made.

    [Dereference] arguments (advancing a list tail via [*(d_a1)]) are NOT moved
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

    What an argument moves of a parameter the ownership plan decides, and
    [args] spell it already ({!moving_jumps}).  [last_reads] are the locals of the turn the
    plan lets the jump move into a parameter's next value at the last of
    the updates reading them by name
    ({!Ownership_ir.Continue_move.Move_argument}): which that is, the
    order the updates are made in says.  One assigned whole to a shadow
    kept by value, or to a temporary, by that update is moved. *)
let make_shadow_updates ?(aliases = []) ?(derefs = []) ?(last_reads = []) shadow_params args =
  let shadow_ids = List.map (fun (id, _) -> id) shadow_params in
  let is_self_assign shadow_id arg =
    match arg with
    | Local id when Id.equal id shadow_id -> true
    | Move (Local id) when Id.equal id shadow_id -> true
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
    let core = match arg with Move a -> a | a -> a in
    (* The shadow's declared type still carries the parameter's [const &]; the
       shadow itself is an owning value of the stripped type. *)
    let vty = strip_ref_and_const_type ty in
    let dereference = function
      | Dereference _ -> true
      | Local v -> List.exists (fun (x, _) -> Id.equal v x) derefs
      | _ -> false
    in
    match (ty, core) with
    | Pointer _, _ -> arg
    | _, core when dereference core && is_value_type_ret vty ->
      converting_ctor vty [core]
    | _ -> arg
  in
  let by_value id = List.exists (fun (s, ty) -> Id.equal s id && not (pointer ty)) shadow_params in
  let moved_at_last_read updates =
    fst
      (List.fold_right
         (fun s (after, read) ->
           let last v = List.exists (Id.equal v) last_reads && not (List.exists (Id.equal v) read) in
           let s =
             match s with
             | Bind_variable (x, Existing, Local v) when by_value x && last v -> Bind_variable (x, Existing, Move (Local v))
             | Bind_variable (x, (Declare (ty, _) as d), Local v) when (not (pointer ty)) && last v ->
               Bind_variable (x, d, Move (Local v))
             | s -> s
           in
           let reads = match s with Bind_variable (_, _, e) | Expression e -> free_vars_expr e | _ -> [] in
           (s :: after, reads @ read) )
         updates ([], []))
  in
  moved_at_last_read @@
  if List.length non_trivial <= 1 then
    (* 0 or 1 assignment: no hazard possible, assign directly *)
    List.filter_map
      (fun ((shadow_id, ty), arg) ->
        if is_self_assign shadow_id arg then None
        else Some (Bind_variable (shadow_id, Existing, make_rhs ty arg)) )
      pairs
  else (* 2+ assignments: use temporaries only where needed *)
    (* Whether [e] reads one of the variables [names]. *)
    let rec mentions names e =
      match e with
      | Local v -> List.exists (Id.equal v) names
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
              (Bind_variable
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
            Some (Bind_variable (shadow_id, Existing, make_rhs ty arg)))
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
                Local (temp_name shadow_id)
              else
                Move (Local (temp_name shadow_id))
            in
            Some (Expression (Binary (Assign, Local shadow_id, rhs)))
          else
            None)
        non_trivial
    in
    temp_decls @ direct_assigns @ temp_updates

(** {2 Generic return-statement rewriter}

    The tail-recursion and TMC loopification passes share the same structural
    traversal of [If], [Custom_match], [Match] and [Block].  They differ
    only in how they handle [Return]:
    tail recursion returns the value directly, while TMC ({!Loopify_tmc})
    patches a write pointer or allocates cells with holes.

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

  rc_shadow_params : (Id.t * ty) list;
  (** Shadow variable bindings [(name, type)] for varying parameters.
      Used by {!make_shadow_updates} when rewriting tail calls. *)

  rc_jumped : expr -> unit;
  (** Told each recursive call rewritten into a jump. *)

  rc_last_reads : expr -> expr list -> Id.t list;
  (** The locals a recursive call passing the arguments given may move at
      their last read among its shadow updates ({!make_shadow_updates}). *)
}

(** Top-level rewrite configuration.  Combines a {!loop_rewrite_config}
    (used for match-branch bodies) with top-level-specific behaviour. *)
type top_rewrite_config = {
  trc_inner : loop_rewrite_config;
  (** Inner config for rewriting match-branch bodies. *)

  trc_jump :
    derefs:(Id.t * expr) list -> updates:(expr list -> stmt list) -> expr -> expr list -> stmt list;
  (** The statements a recursive call [e] in tail position passing [args],
      every parameter's, becomes, under the references to a dereference
      [derefs] declared before it, where [updates args] are the shadow
      updates passing [args] ({!make_shadow_updates}).  Plain tail recursion
      falls through to the [while (true)] test after them; TMC continues. *)

  trc_on_other : derefs:(Id.t * expr) list -> expr -> stmt;
  (** Emit code for a non-tail, non-visit return at the top level, under
      the references to a dereference [derefs] declared before it
      ({!make_shadow_updates}).  Wraps in [Block] as needed. *)

  trc_rewrite_branch : branch -> branch;
  (** Transform a match branch at the top level. *)

  trc_detect_void_tail : bool;
  (** Whether to detect the void tail-call pattern
      [Expression call; Return _] at the list level and rewrite it as
      [Return (Some call)].  Enabled for plain tail recursion; disabled
      for TMC. *)
}

(** Generic top-level statement rewriter.

    Rewrites every [Return] in tail position of the loop body under [trc]:
    a recursive call becomes [trc.trc_jump], anything else
    [trc.trc_on_other].
    {ul {- Returns a single [stmt] (wrapping in [Block] as needed).}
        {- Recurses through [If], [Switch], [Custom_match], [Match] and
           [Block]; other statements are left alone.}
        {- Uses {!generic_rewrite_stmts} for list-level recursion, which
           optionally detects the void tail-call pattern.}}

    [aliases] are the binders inside the storage of a shadow kept by value,
    each with its shadow, and [derefs] the references to a dereference in
    scope ({!make_shadow_updates}). *)
let rec generic_rewrite_stmt ?(aliases = []) ?(derefs = []) trc = function
  | Return (Some e) ->
    ( match trc.trc_inner.rc_check e with
    | Some cs ->
      trc.trc_inner.rc_jumped e;
      let updates args =
        make_shadow_updates ~aliases ~derefs ~last_reads:(trc.trc_inner.rc_last_reads e cs.cs_args)
          trc.trc_inner.rc_shadow_params
          (filter_by_mask trc.trc_inner.rc_varying args)
      in
      Block (trc.trc_jump ~derefs ~updates e cs.cs_args)
    | None -> trc.trc_on_other ~derefs e )
  | If {condition = cond; then_ = then_br; else_ = else_br} ->
    let rw = generic_rewrite_stmts ~aliases ~derefs trc in
    If {condition = cond; then_ = rw then_br; else_ = rw else_br}
  | Switch {scrutinee = scrut; enum = r; branches = branches; default = default} ->
    let rw = generic_rewrite_stmts ~aliases ~derefs trc in
    Switch {scrutinee = scrut; enum = r; branches = List.map (fun (id, body) -> (id, rw body)) branches; default = (* The default branch returns too: left as it was, its [return]
           would leave a tail-modulo-cons loop with the list built so far
           dropped. *)
        Option.map rw default}
  | Custom_match m ->
    let rw = generic_rewrite_stmts ~aliases ~derefs trc in
    Custom_match {m with branches = List.map (fun (b : custom_branch) -> {b with body = rw b.body}) m.branches}
  | Match (scrut, branches, default) ->
    (* A match on the storage of a shadow kept by value binds into it: its
       bindings are aliases of the shadow while the branch runs, and
       overwriting the shadow overwrites them.  A pointer shadow is only
       repointed; what it pointed at stays where it was. *)
    let by_value =
      List.filter_map
        (fun (id, ty) -> if pointer ty then None else Some id)
        trc.trc_inner.rc_shadow_params
    in
    let root =
      storage_root
        ~root:(fun x -> List.exists (Id.equal x) by_value)
        ~bound:(fun x -> List.assoc_opt x aliases)
        scrut.expr
    in
    let inside (br : branch) =
      match root with
      | None -> aliases
      | Some s ->
        let bound = List.map (fun (fb : field_binding) -> fb.name) br.field_bindings in
        let bound = match br.var with Some v -> v :: bound | None -> bound in
        List.map (fun b -> (b, s)) bound @ aliases
    in
    Match (
      scrut,
      List.map
        (fun (br : branch) ->
          let br' = trc.trc_rewrite_branch br in
          { br' with body = generic_rewrite_stmts ~aliases:(inside br') ~derefs trc br'.body })
        branches,
      Option.map (generic_rewrite_stmts ~aliases ~derefs trc) default)
  | Block stmts ->
    Block (generic_rewrite_stmts ~aliases ~derefs trc stmts)
  | s -> s

(** List-level top-level rewriter.

    Optionally detects the void tail-call pattern [Expression call; Return _]:
    {v  call(); return;       (* void tail call *)
    call(); return val;   (* ITree unit-continuation variant *)  v}

    Both forms are rewritten as [Return (Some call)] so the statement-level
    rewriter can handle them as ordinary tail calls.  This pattern is produced
    by [cofix_wrap] and [gen_stmts] for void-returning recursive functions. *)
and generic_rewrite_stmts ?(aliases = []) ?(derefs = []) trc = function
  | Expression e :: Return _ :: rest
    when trc.trc_detect_void_tail && trc.trc_inner.rc_check e <> None ->
    generic_rewrite_stmt ~aliases ~derefs trc (Return (Some e))
    :: generic_rewrite_stmts ~aliases ~derefs trc rest
  | s :: rest ->
    let s' = generic_rewrite_stmt ~aliases ~derefs trc s in
    let derefs =
      match s with
      | Bind_variable (id, Declare (ty, _), Dereference pointer) when is_reference_type ty -> (id, pointer) :: derefs
      | _ -> derefs
    in
    s' :: generic_rewrite_stmts ~aliases ~derefs trc rest
  | [] -> []

(** Wrap a statement list as a single statement. *)
let wrap_as_block = function
  | [s] -> s
  | ss -> Block ss

(** Rewrite a statement list for plain tail-call loopification.

    Constructs a tail-recursion {!top_rewrite_config} and delegates to
    {!generic_rewrite_stmts}.  Base returns return their value directly
    ({!return_result}); tail calls update shadow variables with no
    suffix (control falls through to the [while (true)] test).  Void
    tail-call detection is enabled.  [jumped] is told each call rewritten
    into a jump, and [last_reads] fills [rc_last_reads]. *)
let rewrite_visit_stmts ?(last_reads = fun _ _ -> []) ~jumped check varying shadow_params =
  let inner_rc =
    { rc_check = check;
      rc_varying = varying;
      rc_shadow_params = shadow_params;
      rc_jumped = jumped;
      rc_last_reads = last_reads }
  in
  generic_rewrite_stmts
    { trc_inner = inner_rc;
      trc_jump = (fun ~derefs:_ ~updates _ args -> updates args);
      trc_on_other = (fun ~derefs:_ e -> wrap_as_block (return_result e));
      trc_rewrite_branch = Fun.id;
      trc_detect_void_tail = true }

(** Returns true if the statement declares a new variable or type binding. *)
let declares_variable = function
  | Declare _ | Declare_value_initialized _ | Structured_binding _ | Local_struct _ | Local_type_alias _ -> true
  | Bind_variable (_, Declare _, _) -> true (* typed assignment = declaration *)
  | _ -> false

(** Names declared directly by a statement (not recursing into sub-statements). *)
let direct_decl_ids = function
  | Declare (id, _, _) | Declare_value_initialized (id, _) -> [ id ]
  | Bind_variable (id, Declare _, _) -> [ id ]
  | Local_type_alias (id, _) -> [ id ]
  | Structured_binding (ids, _) -> ids
  | _ -> []

(** Returns true if inlining [block_stmts] before [rest] at the same scope level
    would produce a duplicate declaration.  A conflict arises when a name first
    declared inside [block_stmts] also appears as a top-level declaration in
    [rest] (including inside [Block] nodes in [rest] that would themselves be
    inlined). *)
let would_conflict block_stmts rest =
  if not (List.exists declares_variable block_stmts) then false
  else
    let block_ids = List.concat_map direct_decl_ids block_stmts in
    let rest_ids =
      List.concat_map
        (function
          | Block ss -> List.concat_map direct_decl_ids ss
          | s -> direct_decl_ids s)
        rest
    in
    List.exists (fun id -> List.mem id rest_ids) block_ids

(** Remove unnecessary [Block] wrappers throughout a statement list.

    An [Block] wrapper is unnecessary, and can be inlined into the surrounding
    list, when doing so would not introduce a duplicate declaration at the
    enclosing scope level.  Concretely:

    - [Block []] is always dropped.
    - [Block stmts] is inlined when none of its declared names would clash with
      a name declared by any sibling statement in the enclosing list.  Since each
      [if]/[else]/[while] branch already provides its own [{}] scope in the emitted
      C++, inner blocks inside those branches are almost always safe to remove.

    Recurses into [If], [Switch], [Custom_match], [Match], and [While] so
    that blocks nested inside branches are also simplified. *)
let rec strip_unnecessary_blocks = function
  | Block stmts :: rest ->
    let inner' = strip_unnecessary_blocks stmts in
    let rest' = strip_unnecessary_blocks rest in
    ( match inner' with
    | [] -> rest'
    | _ when not (would_conflict inner' rest') -> inner' @ rest'
    | _ -> Block inner' :: rest' )
  | s :: rest -> strip_loopify_stmt s :: strip_unnecessary_blocks rest
  | [] -> []

(** Recursively strip unnecessary blocks from a single statement's sub-branches
    ([If], [Switch], [Custom_match], [Match], [While], nested [Block]). *)
and strip_loopify_stmt = function
  | If {condition = cond; then_ = then_br; else_ = else_br} ->
    If {condition = cond; then_ = strip_unnecessary_blocks then_br; else_ = strip_unnecessary_blocks else_br}
  | Switch {scrutinee = scrut; enum = r; branches = branches; default = default} ->
    Switch {scrutinee = scrut; enum = r; branches = List.map (fun (id, body) -> (id, strip_unnecessary_blocks body)) branches; default = Option.map strip_unnecessary_blocks default}
  | Custom_match m ->
    Custom_match
      { m with
        branches = List.map (fun (b : custom_branch) -> {b with body = strip_unnecessary_blocks b.body}) m.branches }
  | Match (scrut, branches, default) ->
    Match
      ( scrut,
        List.map
          (fun (br : branch) -> { br with body = strip_unnecessary_blocks br.body })
          branches,
        Option.map strip_unnecessary_blocks default )
  | While (cond, body) -> While (cond, strip_unnecessary_blocks body)
  | Block stmts ->
    (* Reached when an Block appears as a non-first element inside another
       statement (rare; the list-level case above handles the common path). *)
    let stmts' = strip_unnecessary_blocks stmts in
    ( match stmts' with
    | [] -> Block []
    | [ s ] -> s
    | _ -> Block stmts' )
  | s -> s

(** {3 Shadow variable setup}

    Both {!transform_tail} and {!Loopify_tmc.transform_tmc} begin with an identical preamble:
    take which parameters vary across recursive calls, compute pointer-safety
    flags, derive shadow variable names and types, and build the substitution map.
    This shared preamble is factored into {!build_shadow_setup}. *)

(** Result of the shared shadow-variable preamble for tail and TMC transforms.

    Every field is purely derived from the function's parameters and the
    loop's plan; no mutation, no side effects.  The record is consumed
    immediately by the caller to build shadow declarations and substitute
    parameter references. *)
type shadow_setup = {
  ss_varying : bool list;
      (** Bitmask parallel to [params]: [true] when the parameter changes
          across recursive calls and needs a shadow variable. *)
  ss_varying_params : (Id.t * ty) list;
      (** Only the varying parameters (filtered by {!ss_varying}). *)
  ss_shadow_params : (Id.t * ty) list;
      (** Shadow variable names ([_loop_X]) and types for each varying
          parameter, respecting pointer-safety (borrowed params become
          [const T*] shadows). *)
  ss_subs : (Id.t * Id.t) list;
      (** Substitution list: [(original_id, shadow_id)] pairs.  Applied to
          the function body via {!Loopify_analysis.subst_stmt} so that
          references to the original parameter are redirected to the shadow
          variable. *)
}

(** The jumps [check] finds, each moving into the next value of a shadow
    kept by value the shadow itself where the plan moves it there
    ({!Ownership_ir.continue_moves}): [moves] gives, by the occurrence of
    the call a jump is made of, a flag for each of [params], the shadows'
    names [subs] stand for.  The argument reads the shadow once, outside any
    closure and not already moved; reading it otherwise it is left, and
    where that is a spelling the plan's one read does not account for --
    no read, or two, or one in another argument -- reported under
    [CRANE_CHECK_IR]. *)
let moving_jumps ~moves ~subs ~shadow_params params (check : call_checker) : call_checker =
  if moves = [] then check
  else
    let by_value shadow =
      match List.assoc_opt shadow shadow_params with Some ty -> not (pointer ty) | None -> false
    in
    let move_read x arg =
      let bare = ref 0 and moved = ref 0 and captured = ref 0 in
      let rec count = function
        | Move (Local y) -> if Id.equal x y then incr moved
        | Lambda _ as l -> if List.exists (Id.equal x) (free_vars_expr l) then incr captured
        | Move _ -> ()
        | Local y -> if Id.equal x y then incr bare
        | e -> iter_expr_children ~on_expr:count ~on_stmts:(fun _ -> ()) e
      in
      count arg;
      let rec move_in = function
        | (Move _ | Lambda _) as e -> e
        | Local y as e when Id.equal x y -> Move e
        | e -> map_expr move_in Fun.id Fun.id e
      in
      if !bare = 1 then move_in arg
      else begin
        (* Translation moved it already, the parameter being owned there; or
           the read is inside a closure translation made around it -- a
           partial application eta-expanded -- whose capture takes it as
           the plan's captures say ({!Ownership_ir.captures}). *)
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
              (fun k ((move, (id, _)), arg) ->
                match (List.assoc_opt id subs, (move : Ownership_ir.Continue_move.t)) with
                | Some shadow, Move_parameter when by_value shadow ->
                  if spelled_elsewhere k shadow then begin
                    Probe.violation "ownership plan"
                      Pp.(str "a jump the plan moves " ++ Id.print shadow ++ str " into its next value at reads it in another argument");
                    arg
                  end
                  else move_read shadow arg
                | Some _, _ | None, _ -> arg )
              (List.combine (List.combine flags params) site.cs_args)
          in
          Some {site with cs_args = args}
        | Some _ | None -> Some site )
      | None -> None

(** The locals a jump made of a recursive call [e] passing [args] may move
    at their last read among its updates: those passed whole where the plan
    says [Move_argument] ({!Ownership_ir.continue_moves}), [moves] giving,
    by the occurrence of the call, what it moves into each parameter. *)
let planned_last_reads ~moves e args =
  match
    Option.bind (made_of e) (fun o ->
        List.find_map (fun (o', flags) -> if Miniml.Occurrence.equal o o' then Some flags else None) moves )
  with
  | Some flags when List.compare_lengths flags args = 0 ->
    List.concat
      (List.map2
         (fun (move : Ownership_ir.Continue_move.t) arg ->
           match (move, arg) with
           | Move_argument, (Local x | Move (Local x)) -> [x]
           | _ -> [] )
         flags args )
  | Some _ | None -> []

(** Compute the shadow-variable setup shared by {!transform_tail} and
    {!Loopify_tmc.transform_tmc}.

    Computes pointer-safety flags (whether a parameter can be borrowed as
    [const T*] instead of copied, {!pointer_safe_flags}), derives shadow
    variable names ([_loop_X]) and types, and builds the old-to-new
    substitution list.

    @param varying Which parameters the recursive calls change, parallel to
                   [params], as the loop's ControlIR says
    @param parts   Which parameters every recursive call passes a part of
                   what the caller passed ({!pointer_safe_flags})
    @param tparams The surrounding template header, for callable parameters'
                   shadow types ({!tail_shadow_type})
    @param params  Function parameters [(id, type)]
    @return {!shadow_setup} record consumed by the caller *)
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

    A parameter can vary across recursive calls and still never be read (an
    index carried along only to keep a dependent type well-formed, say).  Its
    shadow is then set but never used, which [-Werror] rejects.  Remove both
    the declaration and the writes, iterating so that a staging temporary
    ([_next_x]) left dead by the removal goes too.

    @return the surviving declarations and the rewritten body *)
let drop_unread_shadows shadow_decls body =
  let declared_id = function
    | Bind_variable (id, _, _) -> Some id
    | _ -> None
  in
  let write_target = function
    | Bind_variable (id, _, _) | Expression (Binary (Assign, Local id, _)) -> Some id
    | _ -> None
  in
  (* Every variable the statements *read*: the target of an assignment is a
     write, so only right-hand sides are walked. *)
  let reads stmts =
    let tbl = Hashtbl.create 16 in
    let rec walk_expr e =
      match e with
      | Local id -> Hashtbl.replace tbl (Id.to_string id) ()
      | _ -> iter_expr_children ~on_expr:walk_expr ~on_stmts:walk_stmts e
    and walk_stmt s =
      match s with
      | Bind_variable (_, _, rhs) | Expression (Binary (Assign, Local _, rhs)) ->
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
      if live s then map_stmt Fun.id drop Fun.id s else Block []
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

    {b Non-void functions} return from inside the loop: a base case returns
    its value directly ({!return_result}), and [while (true)]
    without [break] never falls through, so no [_result] or trailing return
    is needed:

    {v
    let rec f x = if base(x) then result else f(next(x))
    ->
    auto _loop_x = x;
    while (true) {
      if (base(_loop_x)) { return result; }
      else { _loop_x = next(_loop_x); }
    }
    v}

    {b Void functions} (e.g. cofixpoint [spin], [forever]) exit via
    [return;] ([Return None]), and a trailing [return;] follows the loop:

    {v
    CoFixpoint forever n := Tau (forever (S n))
    ->
    auto _loop_n = n;
    while (true) { _loop_n = _loop_n + 1; }
    return;
    v}

    After rewriting, {!strip_unnecessary_blocks} removes any empty
    [Block]s left by tail-call rewrites that produced no shadow updates
    (e.g. a zero-parameter cofixpoint like [spin] whose only recursive call
    has no arguments to update), and {!drop_unread_shadows} removes shadows
    the body only writes.

    @param param_inits Optional custom initializers for shadow variables
                       (default: copy from original parameter)
    @param jumped Told each recursive call rewritten into a jump
    @param moves What each jump moves into each parameter's next value, by
                 the occurrence of the call ({!Ownership_ir.continue_moves})
    @param varying Which parameters the recursive calls change, parallel to
                   [params]
    @param parts Which parameters every recursive call passes a part of
                 what the caller passed ({!pointer_safe_flags})
    @param tparams The surrounding template header
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
  let is_void = ret_ty = Void in
  (* Shadow variable declarations (only for varying params) *)
  let shadow_decls =
    List.map2
      (fun (orig_id, ty) (shadow_id, shadow_ty) ->
        let init_expr =
          match List.assoc_opt orig_id param_inits with
          | Some custom -> custom
          | None -> tail_shadow_init orig_id shadow_ty ty
        in
        Bind_variable
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
     pattern [Expression call; Return None] -> [Return (Some call)]) *)
  let check = moving_jumps ~moves ~subs ~shadow_params params check in
  let body'' =
    rewrite_visit_stmts ~last_reads:(planned_last_reads ~moves) ~jumped check varying shadow_params body'
  in
  let body'' = strip_unnecessary_blocks body'' in
  (* Assemble the loop body.
     - Non-void: [... while (true) { ... return val; }]
     - Void:     [... while (true) { ... } return;]
     Non-void base cases return directly via [Return] (from
     [return_result]); no [_result] variable or trailing return needed
     since [while (true)] without [break] never falls through.
     Void base cases exit via [Return None] (plain [return;]).
     Both use [while (true)] for the loop condition. *)
  let shadow_decls, body'' = drop_unread_shadows shadow_decls body'' in
  let body'' = strip_unnecessary_blocks body'' in
  shadow_decls
  @ [While (Literal (Bool true), body'')]
  @ (if is_void then [Return None] else [])

(* Non-tail recursion uses a frame-based stack with [CraneEnter] and
   continuation variants and a dispatch loop; see
   {!Loopify_frame.transform_nontail}. *)

