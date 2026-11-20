(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Lambda parameters and captures: the C++ type a lambda declares each
    parameter at (slot refinement, the type a match reads the binder at,
    erased domains), whether a binder is emitted at all, and the by-value
    captures of a closure that is returned. *)

open Base.Common
open Names
open Util
open Base.Type_util
open Core_plan.Query
open Base.Table

(** Whether a reference was methodified: spelled [x.f(...)] rather than
    [f(x, ...)]. *)
let is_methodified r = Unit_plan.Cpp_names.lookup_method_this_pos r <> None

(** [stmts], a body, whose returned lambdas hold copies ([\[=\]]) rather
    than references into the frame they were written in, which they
    outlive.  Where each lambda is made, Core has decided what it captures:
    a lambda the program writes is a closure; one holding
    references -- the lambdas of a local fixpoint generated in place
    ({!Core_plan.Closures.In_place}), a lambda invoked where it is written, a
    single-use eta-expansion a let binds -- runs where it is written, and
    no body returns it.  A lambda invoked where it is written is not
    returned, whatever its result is: only what {e it} returns is looked
    at.

    Under [CRANE_CHECK_IR], a returned lambda holding references is a
    violation.  It is made a closure all the same, so that no build returns
    references into a frame that is gone. *)
let return_captures_by_value (stmts : Cpp_ir.Lowered.Stmt.t list) : Cpp_ir.Lowered.Stmt.t list =
  let closure (l : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t) : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t =
    match l.capture with
    | Runs_in_place ->
      Base.Probe.violation "closure capture" (Pp.str "a lambda holding references into its frame is returned");
      {l with capture = Stored}
    | _ -> l
  in
  let args f es = List.rev (List.map f (List.rev es)) in
  let rec by_value (l : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t) = closure {l with body = List.map stmt l.body}
  and expr (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
    match e with
    | Lambda l -> Lambda (by_value l)
    | Call (res, Lambda l, es) -> Call (res, Lambda {l with body = List.map stmt l.body}, args expr es)
    | Call (res, f, es) ->
      let es = args expr es in
      let f = expr f in
      Call (res, f, es)
    | Dereference e -> Dereference (expr e)
    | Move e -> Move (expr e)
    | Forward (ty, e) -> Forward (ty, expr e)
    | Aggregate a -> Aggregate {a with values = List.map expr a.values}
    | Local_aggregate a -> Local_aggregate {a with values = List.map expr a.values}
    | Binary (op, a, b) -> Binary (op, expr a, expr b)
    | Unary (op, e) -> Unary (op, expr e)
    | Access (Dot, e, id) -> Access (Dot, expr e, id)
    | Scope (e, id, []) -> Scope (expr e, id, [])
    | Member (e, id) -> Member (expr e, id)
    | Project (e, id, ty) -> Project (expr e, id, ty)
    | Access_call (Arrow, e, id, es) -> Access_call (Arrow, expr e, id, List.map expr es)
    | Any_cast (ty, e) -> Any_cast (ty, expr e)
    | e -> e
  and stmt (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
    match s with
    | Return (Some e) -> Return (Some (expr e))
    | Expression e -> Expression (expr e)
    | If i -> If {condition = expr i.condition; then_ = List.map stmt i.then_; else_ = List.map stmt i.else_}
    | Switch w ->
      Switch
        { w with
          scrutinee = expr w.scrutinee;
          branches = List.map (fun (id, body) -> (id, List.map stmt body)) w.branches;
          default = Option.map (List.map stmt) w.default }
    | Match (scrut, branches, default) ->
      Match
        ( {scrut with expr = expr scrut.expr},
          List.map (fun (br : _ Cpp_ir.Stmt.Match.branch) -> {br with body = List.map stmt br.body}) branches,
          Option.map (List.map stmt) default )
    | Custom_match c ->
      Custom_match
        { c with
          scrutinee = expr c.scrutinee;
          branches =
            List.map (fun (b : _ Cpp_ir.Stmt.Custom_match.branch) -> {b with body = List.map stmt b.body}) c.branches }
    | s -> s
  in
  List.map
    (fun (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t ->
      match s with
      | Return (Some (Lambda ({capture = Runs_in_place; _} as l))) -> Return (Some (Lambda (closure l)))
      | Return (Some e) -> Return (Some (expr e))
      | s -> s )
    stmts

(** Whether [t] still has a hole extraction left open. *)
let rec has_open_meta t =
  match t with
  | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
  | Core.Type.Meta {contents = Some t} -> has_open_meta t
  | Core.Type.Arrow {parameter = a; result = b} -> has_open_meta a || has_open_meta b
  | Core.Type.Global_app {type_arguments = ts; _} -> List.exists has_open_meta ts
  | _ -> false

(** [slot_refined_lambda env ~expected_core_ty args body] -- the binders [args]
    (innermost first) of a lambda over [body], and [body], as lowering
    generates them in a slot of Core type [expected_core_ty]
    ({!Lambda.gen_lambda}; [None] where the slot is a box
    or states none).

    A binder's recorded type is whatever extraction managed to infer for it,
    and a component it never inferred stays erased even where the rest of the
    type is spelled in full: [pair(list(pair(A, B)), Core.Type.Erased)] for a [x] the
    callee declares at [pair(list(pair(A, B)), list(B))].  The slot states the
    whole shape, so the binder is refined against it -- at the {e Core} type,
    before anything reads it.  The signature and the body are generated from
    this one type: correct it at the declaration and the body decomposes the
    pair at the type it really has, while correcting the spelling alone
    leaves the body unboxing at the erased view its own generation assumed
    (see {!Base.Type_util.refine_param_from_slot}, which for that reason may
    only refine as far as still-erased).  A signature's domains are in source
    order, so they index [args] the opposite way.

    A variable of the callee's the slot names and this scope does not --
    [TFunctor_block]'s [U], its instance emitted at [std::any] -- is erased
    where it sits, so the rest of the slot still describes the lambda.  Only
    where extraction left a binder open is it read at that erased view: an
    erased position is no information about a binder that has a type of its
    own ([state_get]'s [s : T1]).  A hole a binder's type is filled at is the
    hole the other binders' and the body's annotations mention -- the match
    destructuring the binder among them -- so they are filled too. *)
let slot_refined_lambda cx env ~expected_core_ty args body =
  let rec erase_unscoped t =
    match resolve_meta t with
    | Core.Type.Variable _ as v
      when not (Types.names_only_scoped_tvars cx (Types.cpp_of_core cx env v)) ->
      Core.Type.Unknown
    | Core.Type.Arrow {parameter = a; result = b} ->
      Core.Type.Arrow {parameter = erase_unscoped a; result = erase_unscoped b}
    | Core.Type.Global_app {head = g; type_arguments = ts; index_arguments = l} ->
      Core.Type.Global_app {head = g; type_arguments = List.map erase_unscoped ts; index_arguments = l}
    | t -> t
  in
  let fills = ref [] in
  let args =
    match expected_core_ty with
    | Some fn_ty ->
      let rec domains ty =
        match resolve_meta ty with
        | Core.Type.Arrow {parameter = d; result = cod} -> d :: domains cod
        | _ -> []
      in
      let doms = Array.of_list (domains fn_ty) in
      let n = List.length args in
      List.mapi
        (fun i (x, ty) ->
          if n - 1 - i >= Array.length doms then (x, ty)
          else
            let d = doms.(n - 1 - i) in
            let d = if has_open_meta ty then erase_unscoped d else d in
            let writable t = Types.names_only_scoped_tvars cx (Types.cpp_of_core cx env t) in
            (x, Base.Type_util.refine_erased ~fills ~writable ty d) )
        args
    | None -> args
  in
  let args = List.map (fun (x, t) -> (x, Base.Type_util.fill_holes_type !fills t)) args in
  (args, Base.Type_util.fill_holes !fills body)

(* Whether [body] takes its single binder apart: matches on it, or applies to
   it a projection spelled as member access (an inline custom [%a0.first]). *)
let body_reads_members_of_binder body =
  let member_access g =
    Base.Table.is_inline_custom g
    && ( match Base.Table.find_custom_opt g with
       | Some txt ->
         String.length txt > 4 && String.sub txt 0 4 = "%a0."
       | None -> false )
  in
  let rec reads depth e =
    match e with
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _};
                       arguments = Core.Expr.Bound_variable {index = k; _} :: _}
      when k = depth + 1 && member_access g ->
      true
    | Core.Expr.Lambda {body = b; _} -> reads (depth + 1) b
    | Core.Expr.Let {value = x; body = b; _} -> reads depth x || reads (depth + 1) b
    | Core.Expr.Match {scrutinee = sc; branches = pv; _} ->
      reads depth sc
      || Array.exists
           (fun {Core.Match.Branch.binders = ids; body = br; _} -> reads (depth + List.length ids) br)
           pv
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
      Array.exists (reads (depth + Array.length ids)) funs
    | e ->
      let found = ref false in
      Base.Core_util.ast_iter (fun x -> if reads depth x then found := true) e;
      !found
  in
  (match body with
   | Core.Expr.Match {scrutinee = Core.Expr.Bound_variable {index = 1; _}; branches = pv; _} -> is_custom_match pv
   | _ -> false)
  || reads 0 body

(* The type a match in [body] reads its single binder at, where that type has
   no parameters -- and so one spelling, which the body cannot be reading at
   some other, erased, view: [if b] states [bool] whatever the binder's own
   annotation lost. *)
let binder_matched_at body =
  let found = ref None in
  let rec walk depth e =
    match e with
    | Core.Expr.Match {scrutinee_type = (Core.Type.Global_app {type_arguments = []; _} as t); scrutinee = sc; _}
      when (match strip_magic sc with Core.Expr.Bound_variable {index = j; _} -> j = depth + 1 | _ -> false)
           && !found = None ->
      found := Some t
    | Core.Expr.Lambda {body = b; _} -> walk (depth + 1) b
    | Core.Expr.Let {value = x; body = b; _} -> walk depth x; walk (depth + 1) b
    | Core.Expr.Match {scrutinee = sc; branches = pv; _} ->
      walk depth sc;
      Array.iter (fun {Core.Match.Branch.binders = ids; body = br; _} -> walk (depth + List.length ids) br) pv
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
      Array.iter (walk (depth + Array.length ids)) funs
    | e -> Base.Core_util.ast_iter (walk depth) e
  in
  walk 0 body;
  !found

(** Whether binder [i] of a lambda's [binders] (innermost-first, over
    [body]) becomes a C++ parameter, the lambda written against a slot of C++
    type [expected_ty] ({!Lambda.gen_lambda}).  A binder typed
    [Core.Type.Erased] carries nothing, unless the body names it or the slot's
    declaration takes a value at its position: [Cat IFun]'s [cat] binds
    objects [a b c] that [obj := Type -> Type] erases, and [Cat] is a
    function of them all the same -- and only where the slot's own domain
    there is a box: an erased binder stands for an erased value, [Id_]'s
    object, never for the [Nat] state a [stateT] takes first.  A binder with
    no type ([Core.Type.Axiom]) is one erasure took the type from -- [IFun]'s
    [forall T] -- and unused it is erased like a dummy.  The count of binders
    the term writes and the parameter list it is written with are both read
    off this, so they cannot disagree. *)
let lambda_binder_emitted cx env ~(expected_ty : Cpp_ir.Lowered.Type.t option) ~body binders i ty =
  let slot_value_doms =
    let rec alias_ref (t : Cpp_ir.Lowered.Type.t) =
      match Cpp_ir.Types.strip_param_spelling t with
      | In_namespace (_, t) -> alias_ref t
      | Entity_application (GlobRef.ConstRef kn, _, _) -> Some kn
      | _ -> None
    in
    let rec value_doms t =
      match resolve_meta (expand_core_fun_alias t) with
      | Core.Type.Arrow {parameter = d; result = c} -> not (erased_by_extraction d) :: value_doms c
      | _ -> []
    in
    match Option.bind expected_ty alias_ref with
    | Some kn -> (
      match Base.Table.lookup_typedef_unchecked kn with
      | Some body -> value_doms body
      | None -> [] )
    | None -> []
  in
  let slot_doms_cpp =
    match Option.map (Types.unfold_cpp_typedef cx env) expected_ty with
    | Some (Function (doms, _)) -> doms
    | _ -> []
  in
  let slot_keeps binders i =
    let d = List.length binders - 1 - i in
    match List.nth_opt slot_value_doms d with
    | Some true -> (
      match List.nth_opt slot_doms_cpp d with
      | Some t -> Cpp_ir.Types.prints_as_any t
      | None -> true )
    | _ -> false
  in
  slot_keeps binders i
  || (is_runtime_binder_type ty && ty <> Core.Type.Axiom)
  || Base.Core_util.ast_occurs (i + 1) body

(** The C++ type a lambda declares its parameter [(id, ty, owned)] at
    ({!Lambda.gen_lambda}), how it is passed, and the substitution its body is
    rewritten with, if any.  [slot_dom] is the domain the slot the lambda
    fills declares at this parameter's position, where it declares a
    signature; [unused], that the body never reads the parameter; [body], the
    lambda's body; [n_params], how many binders it has; [rank2_carrier], the
    template parameter a polymorphic function object writes its erased
    positions at; [reified], that itree terms are extracted reified.  Lowering
    passes what it is generating against, the representation plan what it
    reads off Core. *)
let lambda_param_cpp_type cx env ~ns ~tvars ~rank2_carrier ~reified ~n_params ~body ~unused ~slot_dom (id, ty, owned) =
  let at_carrier ty = match rank2_carrier with None -> ty | Some x -> Rank2.at_carrier x ty in
  let tvar_in_scope n = List.exists (Id.equal n) tvars in
  let slot_param_cpp_ty =
    (* Only a type this lambda could actually be written against.  The slot
       is read off the callee's declaration, so it may name that
       declaration's own template parameters, which are no more in scope here
       than the erasure was -- adopting one trades [std::any] for a free
       name. *)
    match slot_dom with
    | Some t
      when Id.Set.for_all tvar_in_scope (Cpp_ir.Types.variable_names t) ->
      Some t
    | _ -> None
  in
  let bare_cpp_ty =
    Types.cpp_of_core cx env ty
  in
  let stored_cpp_ty =
    Types.cpp_ir_of_core_type cx env ~ns
      tvars ty
  in
  let body_subst =
    match (bare_cpp_ty, stored_cpp_ty) with
    | Entity_application (g1, [], _), Shared_pointer (Entity_application (g2, [], _))
      when globref_equal g1 g2 && Base.Table.is_coinductive g2 ->
      Some (id, (Dereference (Local id) : Cpp_ir.Lowered.Expr.t))
    | _ -> None
  in
  let lent t : Cpp_ir.Lowered.Type.t * Cpp_ir.Param_mode.t =
    (Cpp_ir.Param_mode.declare By_const_reference t, Cpp_ir.Param_mode.lent)
  in
  let param_cpp_ty, mode =
    match body_subst with
    | Some _ -> lent stored_cpp_ty
    (* A binder the body never reads is a parameter only for its callers, and
       the slot's own spelling is the one they call it at:
       [Id_<std::any, ...>] takes its object as a box, whatever the binder's
       annotation recorded -- [MemE], the family the object stands for. *)
    | None when unused && Option.has_some slot_param_cpp_ty ->
      (* Taken as the slot declares it: the mode is the one its type
         spells. *)
      let slot = Option.get slot_param_cpp_ty in
      (slot, Cpp_ir.Param_mode.spelled ~owned slot)
    (* The binder's annotation is a definition unfolded -- [FusedS] as
       [state * nat] -- and a class field in it names no instance in this
       scope, so it would fall back to the file-scope [std::any].  The slot
       writes the definition by name, which its own declaration resolved. *)
    | None
      when Types.mentions_unresolved_promoted cx bare_cpp_ty
           && Option.has_some slot_param_cpp_ty ->
      Ownership.wrap_param_by_ownership cx ~is_owned:owned
        (Option.get slot_param_cpp_ty)
    | None
      when rank2_carrier <> None
           && has_tany_in_type bare_cpp_ty
           && not (Rank2.is_bare_box bare_cpp_ty) ->
      lent (at_carrier bare_cpp_ty)
    | None
      when Cpp_ir.Types.prints_as_any bare_cpp_ty
           && ( match slot_param_cpp_ty with
              | Some d -> not (Cpp_ir.Types.prints_as_any d)
              | None -> false ) ->
      (* The binder's own annotation says nothing -- a constructor eta-expanded
         into a lambda ([fmap inr m]) is handed a parameter extraction never
         gave a type -- but the slot it flows into does: the callee's
         instantiated domain.  Taking the type from there is what keeps the
         signature and the body in step, since the body was generated against
         the concrete type the constructor needs.  Written [std::any] instead,
         the parameter is a claim the body cannot keep, and the error lands
         inside the lambda at the use. *)
      Ownership.wrap_param_by_ownership cx ~is_owned:owned
        (Option.get slot_param_cpp_ty)
    | None
      when Base.Type_util.has_tany_written bare_cpp_ty
           && n_params = 1
           && (body_reads_members_of_binder body || binder_matched_at body <> None) ->
      (* A pattern lambda: the body decomposes this parameter with a
         structured binding, which is ill-formed at [std::any].  Or it reads
         one of its members through a projection that is spelled as member
         access ([fst si] as [si.first]), which is ill-formed there just the
         same.  [crane_erase_fn] probes a generic callable with exactly that --
         and the binding is in the body, not the signature, so no [requires]
         can absorb the failure and the probe becomes a hard error.  Spelling
         the type keeps the probe well-formed: CTAD then deduces a signature,
         and the adapter unboxes at this very type, which is the one the
         producer boxed.

         Which type to spell is the slot's answer where it has one.  The
         binder's own is assembled from a Core type whose erased components
         were never inferred, so it erases a whole component the container
         keeps ([pair<Nat, std::any>] against a list of
         [pair<Nat, Exp0<std::any>>]); the slot spells the container's shape
         and leaves only the genuinely erased leaf to [std::any].

         It may refine the spelling only as far as still-erased, though.  The
         body was generated against the erased view and unboxes at it; a
         signature that erases nowhere is one the body's casts no longer agree
         with.  The exception is a match that reads the binder at a fully
         known type -- [if b] at [bool] -- since the body reads it at that
         type, uncast. *)
      let refined =
        match (binder_matched_at body, slot_dom) with
        | Some t, _ -> Types.cpp_of_core cx env t
        | None, Some slot ->
          Base.Type_util.refine_param_from_slot ~tvars ~slot
            bare_cpp_ty
        | None, None -> bare_cpp_ty
      in
      Ownership.wrap_param_by_ownership cx ~is_owned:owned refined
    | None
      when reified && core_type_is_unit ty ->
      (* A reified tree's continuation is typed [unit -> itree ...] in Core, but
         [unit] is not one C++ type here: the value a reified tree carries is
         whatever its consumer chose, and the same Rocq type reaches the
         printer as [std::monostate] over a concrete tree and as [std::any]
         over one whose event type was erased.  The binder is under-determined
         rather than erased -- nothing in the term says which -- so it
         deduces.  Committing to [std::monostate] rejects every call through
         an erased tree.  The slot is still emitted; see the parameter filter
         in {!Expr.gen_expr}. *)
      lent Auto
    | None when Base.Type_util.has_tany_written bare_cpp_ty ->
      (* The type is spelled with erased positions (std::any).  Use
         [const auto&] so the C++ compiler deduces the concrete type at the
         call site -- explicit std::any in the param type would block valid
         calls and prevent field accesses inside the body from resolving to
         the concrete type.

         The erasure has to be one the spelling shows.  A type whose erased
         argument sits in a position its template never writes renders
         concretely, and a generic parameter there is a liability: a consumer
         that probes the callable with a [std::any] -- [crane_erase_fn] does --
         instantiates the body at [std::any] and fails inside it, where no
         [requires] can catch it. *)
      lent Auto
    | None ->
      (* A function the slot takes at fewer domains than the binder's arrows
         flatten to -- [esc : A -> cont R B], with [cont R B] an alias for a
         function type -- is curried where the slot says ([Declared_at]). *)
      let declared_arity =
        match Option.map (Types.unfold_cpp_typedef cx env) slot_dom with
        | Some (Function (doms, _)) -> List.length doms
        | _ -> 0
      in
      Ownership.wrap_param_by_ownership cx ~is_owned:owned
        (if declared_arity > 0 then Cpp_ir.Types.spell_arrows (Declared_at declared_arity) bare_cpp_ty
         else bare_cpp_ty)
  in
  (param_cpp_ty, mode, body_subst)

(** The C++ type a lambda parameter of Core type [core_ty] declared [declared]
    ({!lambda_param_cpp_type}) is read at in its body.  A binder erasure would
    have removed, kept because the slot takes it ({!binder_emitted}), holds
    whatever box the caller passes.  So does one the slot declares erased
    ([slot_dom]), even though it is declared [const auto &] so the deduction
    can also land on a concrete type: assigned [std::any], uses inside the
    body recover their own type from it, where the [Tauto] the declaration
    strips to would say, wrongly, that the value is already what the body
    wants. *)
let lambda_param_assigned ~slot_dom core_ty (declared : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  if erased_by_extraction core_ty then Any
  else
    match (declared, slot_dom) with
    | Reference (Lvalue, Const Auto), Some d when Cpp_ir.Types.prints_as_any d -> Any
    | _ -> declared
