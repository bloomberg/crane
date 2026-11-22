(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Pattern matches: a match over a variant as a [Match] statement with one
    branch per constructor, or a [Switch] over an enumeration
    ({!gen_cpp_case}); a custom match through its template
    ({!gen_custom_cpp_case}); and a match taking a record apart into its
    fields, in expression and in statement position.  One of the modules
    lowering Core bodies to CppIR that {!Lower_expr} drives; it calls back
    into expression and statement lowering through {!Knot}. *)

open Base.Common
open Names
open Base.Core_util
open Base.Table
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query
open Knot
open Construction

module IntSet = Core_plan.Escape.IntSet

(** How a match branch reads a field of the constructor it matched: as the
   structured binding has it; through the pointer the field is stored behind
   (a recursive field, or under [Crane BoxedFields] one holding an inductive);
   or through [crane::unbox] (a type-parameter field under [Crane
   BoxedFields], boxed or not per instantiation). *)
type field_read = Read_as_bound | Read_through_pointer | Read_unboxed

(** Whether a record's fields are moved out of what [base] reads it from. *)
let moved_out (base : Cpp_ir.Lowered.Expr.t) = match base with Move _ -> true | _ -> false

(** Whether a match taking the record [t] apart, a class instance's fields
   unless [is_typeclass], takes its value, as the plan says
   ({!Ownership_ir.Region.takes_record}); under [CRANE_CHECK_IR], the code reading
   it from [base] must agree. *)
let record_taken cx ~is_typeclass t base =
  let taken = (not is_typeclass) && Ownership_ir.Region.takes_record ~throws:(is_throwing_value cx)
    cx.ctx.lexical.move_plan t in
  if Base.Probe.checking () && taken <> moved_out base then
    Base.Probe.violation "ownership plan"
      (Pp.str
         ( if taken then "a record the plan takes apart by value is read in place"
           else "a record the plan reads in place is taken apart by value" ) );
  taken

(** Runs [f], which generates the body of [case], a match taking a record
   apart into the fields [asgns] declares, under the plan in which each field
   moved out of the record into a local of its own is the body's.  A field
   copied out of a record still held is not: it may be read in place. *)
let with_fields_plan cx case asgns f =
  with_plan cx (Ownership_ir.Region.fields_by_value cx.ctx.lexical.move_plan ~case ~by_value:(List.map snd asgns)) f

(** The return type a branch of a match invoked in place, annotated [rty],
    is written under: the one in force, [ret], where it is a function type;
    failing that, at a function of several arguments, the annotation's, the
    type the match joins its callables at ({!Match_types.iife_closure_return}),
    so that a lambda in the branch's tail takes them all. *)
let branch_return cx env (ret : Cpp_ir.Lowered.Type.t option) (rty : Core.Type.t) =
  match ret with
  | Some (Function _) -> ret
  | _ when count_core_value_arrows rty >= 2 -> (
    match Types.cpp_of_core cx env rty with
    | Function _ as f when Types.names_only_scoped_tvars cx f && not (Base.Type_util.has_tany_written f) -> Some f
    | _ -> ret )
  | _ -> ret

(** The slot a branch annotated [rty] hands its value to: the match's own,
    [slot], which states the Core type a function value is written against
    ({!Lambda.gen_lambda}) where it is one; failing that, at a function type,
    the branch's annotation, which says it as well. *)
let branch_slot ?slot (rty : Core.Type.t) : Slot.slot option =
  let arrow t = match resolve_meta t with Core.Type.Arrow _ -> true | _ -> false in
  match slot with
  | Some ({Slot.expected_core_ty = Some t; _} : Slot.slot) when arrow t -> slot
  | _ when arrow rty ->
    let s = match slot with Some s -> s | None -> Slot.empty_slot in
    Some {s with Slot.expected_core_ty = Some rty}
  | _ -> slot

(** Generate a single branch of a [Match] statement's if/else-if chain.

    Produces a [Cpp_ir.Grammar.Match.branch] whose body statements live directly
    in the enclosing if-block.

    {b Structured bindings.}  Field accesses use
    [const auto& [d_f0, d_f1] = std::get<T>(v)].  The reference binding is
    required so that [[=]]-capturing closures copy the struct value rather
    than a raw pointer that could dangle after the match scope ends.

    {b [match_i] suffix generation.}  [match_i] is the match-level counter
    (0 for the outermost match).  Nested matches increment the counter so
    binding names get suffixed (field [d_a0] binds [d_a00] at level 1, [d_a01] at level 2) to avoid shadowing
    outer bindings.

    {b [dummies] mask.}  A [bool list] parallel to [ids]: [true] means the
    pattern variable is actually used (gets a binding); [false] means it is
    [Core.Binder_name.Anonymous] (omitted from the structured binding with a placeholder).  This
    avoids generating unused variable warnings in the C++ output.

    @param env      current name environment
    @param typ      the scrutinee's Core type (used to resolve the inductive)
    @param rty      the branch's return type
    @param cname    the constructor's [GlobRef.t]
    @param ids      renamed pattern variable names with types
    @param dummies  parallel mask: [true] = non-Dummy (used), [false] = Dummy
    @param body     the branch body AST
    @param sname    scrutinee expression name (for structured binding access)
    @param match_i  nesting level counter for name suffixing
    @param scrut    the value being matched, shared by every branch
    @param site     the match and this branch, binding [ids] *)
let gen_match_branch cx ?slot env (typ : Core.Type.t) rty cname ids dummies body sname
    match_i (scrut : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Match.scrutinee) ~scrut_db ~site :
    Cpp_ir.Lowered.phase Cpp_ir.Grammar.Match.branch =
  let ctor_type = Match_types.ctor_type_of_match cx env typ cname in
  let ctor_name = ctor_struct_id_of_ref cname in
  let ctor_struct_name = Id.to_string ctor_name in
  let n_pat_vars = List.length ids in
  let ind_ref =
    match cname with
    | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
    | r -> r
  in
  let fields = Base.Type_util.Ctor_fields.of_ctor cname in
  let non_erased_def_site_field_tys = fields.types in
  let is_self_or_mutual = Base.Type_util.Ctor_fields.is_self_or_mutual fields in
  let field_is_self_or_mutual_ref_at_def = Base.Type_util.Ctor_fields.self_or_mutual_ref fields in
  let field_has_nested_self_ref_at_def = Base.Type_util.Ctor_fields.nested_self_ref fields in
  let field_recurses_through_boxed_at_def = Base.Type_util.Ctor_fields.recurses_through_boxed fields in
  let is_boxed_at_def = Base.Type_util.Ctor_fields.boxed fields in
  let is_param_boxed_at_def = Base.Type_util.Ctor_fields.param_boxed fields in
  (* Compute structured binding names BEFORE the body, so that inner nested
     matches see these names in their avoid set and won't produce shadowing
     C++ variable names (e.g. two nested [Char] branches both naming [t0]).
     For match_i=0 the binding name equals the struct field name (e.g. [d_a0]);
     for deeper nesting a numeric suffix prevents collisions
     (e.g. [d_a00] at level 1, [d_a01] at level 2). *)
  let suffix =
    if match_i = 0 then "" else string_of_int (match_i - 1)
  in
  let rev_ids = List.rev ids in
  let dummies_arr = Array.of_list dummies in
  let outer_avoid = snd env in
  let binding_names_arr =
    let avoid = ref outer_avoid in
    Array.init (List.length rev_ids) (fun i ->
      let field_id = lookup_ctor_bind_name ~owner:ind_ref ctor_struct_name i in
      let base = Id.of_string (Id.to_string field_id ^ suffix) in
      let name =
        if Id.Set.mem base !avoid then rename_id base !avoid else base
      in
      avoid := Id.Set.add name !avoid;
      name)
  in
  (* Extend env's avoid set with the binding names so inner matches can
     see them and avoid generating the same names (prevents C++ shadowing). *)
  let env_for_body =
    let binding_avoid =
      Array.fold_left (fun acc n -> Id.Set.add n acc)
        outer_avoid binding_names_arr
    in
    (fst env, binding_avoid)
  in
  let body_stmts =
    (
      let inner_ret =
        match current_cpp_return_type cx () with
        | Some Void -> None
        | rt -> branch_return cx env rt rty
      in
      with_scope cx @@ fun () ->
      with_cpp_return_type cx inner_ret (fun () ->
          Match_types.populate_erased_field_env cx
            ?scrut_db:(Option.map (fun db -> db + n_pat_vars) scrut_db)
            ~cname ~typ ~env ~n_pat_vars
            ~n_fields:(List.length rev_ids)
            ~non_erased_def_site_field_tys ();
          if Base.Probe.checking () then
            List.iteri
              (fun i _ ->
                Representation_plan.check cx.ctx ~site ~field:i
                  ~live:(Binders.binder_is_boxed cx (n_pat_vars - i)) () )
              rev_ids;
          gen_stmts cx ?slot:(branch_slot ?slot rty) env_for_body (Destination.return_ cx) body ))
  in
  let tvars = get_current_type_vars cx in
(* A non-self-referential field in a type-indexed inductive (no template
     params) whose def-site type contains an unnamed Core.Type.Variable is stored as
     [std::any] in the struct.  At the match site we recover the Core-known
     type with [std::any_cast<bare_ty>].  This handles every access pattern
     uniformly — fst, snd, or any other function — because the cast is
     applied at the binding site, not at individual use sites. *)
  let scrut_template_args_lazy = lazy (
    let scrut_cpp_ty = Types.cpp_of_core cx env typ in
    extract_template_args scrut_cpp_ty
  ) in
  let field_is_wholesale_erased =
    let num_pv = Base.Table.get_ctor_num_param_vars cname in
    fun i ->
      not (field_is_self_or_mutual_ref_at_def i)
      && not (field_has_nested_self_ref_at_def i)
      && (match List.nth_opt non_erased_def_site_field_tys i with
          | Some def_ty when num_pv = 0 ->
            let cpp_ty =
              Types.cpp_ir_of_core_type cx (empty_env ()) ~ns:(Core.Ref.User.Set.singleton ind_ref) [] def_ty
            in
            has_unnamed_tvar cpp_ty
          | Some (Core.Type.Variable {variable = k; _}) ->
            let scrut_targs = Lazy.force scrut_template_args_lazy in
            (match List.nth_opt scrut_targs (k - 1) with
             | Some t -> Types.resolves_to_any_type cx t
             | None -> false)
          | _ -> false)
  in
  let field_bindings =
    List.mapi
      (fun i (var_name, core_ty) ->
        let binding_name = binding_names_arr.(i) in
        if Base.Probe.checking ()
           && not (Option.equal Id.equal (get_db_name_opt (n_pat_vars - i) env) (Some var_name))
        then
          Base.Probe.violation "match field binder"
            Pp.(str "field " ++ int i ++ str " of " ++ Id.print ctor_name ++ str " is not "
                ++ Id.print var_name ++ str " in its branch's scope");
        (* A field needs dereferencing if:
           1. It's a direct self/mutual ref at the definition site
              (stored as shared_ptr in the struct), OR
           2. The def-site field type is Core.Type.Variable (type parameter) that resolves
              to shared_ptr<T> via template substitution, where T is a
              value-type inductive in method_self_ns.  This happens when a
              container like List<shared_ptr<tree>> stores elements via
              template parameter t_A = shared_ptr<tree>. Direct struct
              fields (Core.Type.Global_app at def-site) are bare value types. *)
        (* Convert using empty ns.  For value-type self/mutual fields the
           expression substituted into the branch body is dereferenced, but the
           structured binding itself still has the stored field type
           [shared_ptr<T>].  Loopify uses this metadata to infer frame field
           types for expressions like [d_a0.get()] and [*d_a0]. *)
        let bare_field_cpp_ty =
          Types.cpp_of_core cx env core_ty
        in
        let storage_field_cpp_ty =
          Types.cpp_ir_of_core_type cx env ~ns:(Core.Ref.User.Set.singleton ind_ref)
            tvars
            core_ty
        in
        (* A non-coinductive field is shared_ptr-wrapped only for UNIFORM
           self-recursion.  Non-uniform recursion (e.g. tree<pair<T,T>> inside
           tree<T>) stores as a bare value type.  Find the self/mutual reference
           anywhere in the Core type (direct or nested in type args) and check if
           its type arguments match the parent's params uniformly. *)
        let is_uniform_self_ref_at_def i =
          match List.nth_opt non_erased_def_site_field_tys i with
          | Some ty -> begin
            match find_self_ref_args ~is_self_or_mutual ty with
            | Some args ->
              let n_params = Base.Table.get_ctor_num_param_vars cname in
              List.length args = n_params
              && List.for_all (fun (j, arg) ->
                match arg with
                | Core.Type.Variable {variable = k; _} -> k = j + 1
                | Core.Type.Meta {contents = Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                                       variable = k})}
                | Core.Type.Meta {contents = Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid;
                                                                       variable = k})} -> k = j + 1
                | _ -> false
              ) (List.mapi (fun j a -> (j, a)) args)
            | None -> true  (* no self-ref found: treat as uniform *)
          end
          | _ -> true
        in
        (* A field boxed for its own type is read like a recursive one. *)
        let is_sptr_self_ref =
          ( ( field_is_self_or_mutual_ref_at_def i
              || field_has_nested_self_ref_at_def i )
            && not (field_recurses_through_boxed_at_def i)
            && is_uniform_self_ref_at_def i
            || is_boxed_at_def i )
          && not (Base.Table.is_coinductive ind_ref)
        in
        (* The struct holds a [crane::field] for a type-parameter field
           unless it erased the field outright. *)
        let is_param_boxed =
          (not is_sptr_self_ref) && is_param_boxed_at_def i
          && (not (Base.Table.is_coinductive ind_ref))
          && (not (field_is_wholesale_erased i))
          && bare_field_cpp_ty <> Cpp_ir.Type.Any
        in
        let field_cpp_ty : Cpp_ir.Lowered.Type.t =
          if is_sptr_self_ref then
            (* All self/mutual refs (direct or nested-in-custom): struct field
               is shared_ptr<bare>.  After deref, the binding has type bare_ty
               which matches the API type directly — no element-wise conversion
               needed.  Using storage_field_cpp_ty here would store inner
               self-refs as shared_ptr<T> inside the custom container, but
               there is no element-wise converter from List<shared_ptr<T>> to
               List<T>, so we must keep elements as bare values. *)
            Shared_pointer bare_field_cpp_ty
          else if is_param_boxed then
            (* The struct stores [crane::field<T>], but the binding is
               [auto] and every read of it goes through [crane::unbox]: as
               the passes after this see it, it is the [T] it holds.  Whether
               that [T] is erased is decided later, and they have to see it
               to cast it. *)
            bare_field_cpp_ty
          else if field_recurses_through_boxed_at_def i then
            (* Boxed-element container field: stored by value as
               flex_vector<box<self>> (matches the struct field decl); the box
               provides the indirection, so no shared_ptr and no deref. *)
            bare_field_cpp_ty
          else
            (* Use storage_field_cpp_ty but correct false-positive shared_ptr
               wrapping: when storage wraps with shared_ptr but the def-site
               check says NOT a self-ref, use bare type instead.
               This happens when a type parameter is instantiated to the same
               inductive (e.g. element List<T> inside List<List<T>>): the element
               field's def-site type is a bare Core.Type.Variable (not self-ref), but at the
               use site it resolves to List<T> which ns-wraps to shared_ptr. *)
            if non_erased_def_site_field_tys <> []
               && not (field_is_self_or_mutual_ref_at_def i)
               && not (field_has_nested_self_ref_at_def i)
               && Convert.contains_shared_ptr storage_field_cpp_ty
            then bare_field_cpp_ty
            else storage_field_cpp_ty
        in
        let used = dummies_arr.(i) in
        let read =
          if is_sptr_self_ref then Read_through_pointer
          else if is_param_boxed then Read_unboxed
          else Read_as_bound
        in
        (binding_name, field_cpp_ty, read, used, core_binder cx ~site env (n_pat_vars - i)))
      rev_ids
  in
  let field_bindings_arr = Array.of_list field_bindings in
  let rec expr_has_lambda (e : Cpp_ir.Lowered.Expr.t) =
    match e with
    | Call (_, Lambda {body = body; _}, _) ->
      (* IIFE: lambda is invoked immediately, so reference captures are safe.
         Only check the lambda body for nested non-IIFE lambdas. *)
      List.exists stmt_has_lambda body
    | Lambda {capture = Stored; _} ->
      (* [=] value-capture: non-coinductive self-ref fields (shared_ptr) need
         pre-extraction into a value binding before the lambda is entered. *)
      true
    | Lambda {body = body; capture = Runs_in_place; _} ->
      (* [&] ref-capture: shared_ptr fields are captured by reference — fine.
         Check the body for nested [=] lambdas that would need pre-extraction. *)
      List.exists stmt_has_lambda body
    (* Only a requires expression's constrained expressions, not the
       constraints on them. *)
    | Requires r -> List.exists (fun (e', _) -> expr_has_lambda e') r.constraints
    | e ->
      let found = ref false in
      Cpp_ir.Children.expr
        { expr = (fun e' -> if expr_has_lambda e' then found := true);
          stmt = (fun s -> if stmt_has_lambda s then found := true);
          type_ = ignore }
        e;
      !found
  and stmt_has_lambda (s : Cpp_ir.Lowered.Stmt.t) =
    match s with
    | Return (Some e) | Expression e -> expr_has_lambda e
    | Bind_variable (_, _, e) -> expr_has_lambda e
    | If {condition = c; then_ = t; else_ = f} ->
      expr_has_lambda c || List.exists stmt_has_lambda t
      || List.exists stmt_has_lambda f
    | Switch {scrutinee = scrut; branches = branches; default = default; _} ->
      expr_has_lambda scrut
      || List.exists (fun (_, body) -> List.exists stmt_has_lambda body) branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Match (scrut, branches, default) ->
      expr_has_lambda scrut.expr
      || List.exists
        (fun (br : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Match.branch) -> List.exists stmt_has_lambda br.body)
        branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Custom_match m ->
      expr_has_lambda m.scrutinee
      || List.exists
           (fun (b : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Custom_match.branch) -> List.exists stmt_has_lambda b.body)
           m.branches
    | Assign (obj, e) -> expr_has_lambda obj || expr_has_lambda e
    | While (c, body) -> expr_has_lambda c || List.exists stmt_has_lambda body
    | Block body -> List.exists stmt_has_lambda body
    | Foreign_block b -> List.exists expr_has_lambda b.values
    | _ -> false
  in
  let branch_has_lambda = List.exists stmt_has_lambda body_stmts in
  (* True when the enclosing function returns a coinductive type and will
     wrap each branch result in a [lazy_] thunk via [cofix_wrap].  The
     thunk is a [Lambda] that captures by [=], so non-coinductive
     self-ref (shared_ptr) fields bound in the branch need pre-extraction
     before the lambda to ensure they are captured as value types.
     This flag triggers pre-extraction even when [branch_has_lambda] is
     false (because the lambda is added externally by [inline_iife]). *)
  let return_type_is_coinductive =
    match current_cpp_return_type cx () with
    | Some (Entity_application (r, _, _)) -> Base.Table.is_coinductive r
    | _ -> false
  in
  let branch_needs_sptr_preextract =
    branch_has_lambda || return_type_is_coinductive
  in
    (* Substitute pattern variable references with the structured-binding
     names.  For non-coinductive self-ref fields (stored as shared_ptr),
     the structured binding gives [const shared_ptr<T>& d_field]; we
     dereference it so the body sees a value reference [const T&] instead.
     This ensures method calls use [.] not [->]. *)
  let body_stmts =
    List.fold_left
      (fun stmts (i, (var_name, _core_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, read, _, _) = field_bindings_arr.(i) in
          let bare_ty = Types.cpp_of_core cx env _core_ty in
          (* Pre-extract fields stored as shared_ptr when the branch body
             contains a lambda (or the return type is coinductive), so the
             lambda captures the value type rather than the shared_ptr.
             Only non-coinductive self-refs (is_uptr = true) need this:
             all formerly-unique_ptr fields have is_uptr set, and shared_ptr
             (coinductive or generic container fields) is copyable and can
             be captured directly. *)
          let is_uptr_field = read = Read_through_pointer in
          let subst_expr : Cpp_ir.Lowered.Expr.t =
            if read = Read_unboxed then
              Cpp_ir.Build.call (Runtime Cpp_ir.Crane_rt.Unbox_field) [Local binding_name]
            else if is_uptr_field && branch_needs_sptr_preextract then
              Local (Id.of_string (Id.to_string binding_name ^ "_value"))
            else if is_uptr_field then
              (* field_ty = Shared_pointer storage_inner.  Deref the outer
                 shared_ptr, then convert storage_inner → bare_ty if they
                 differ (e.g. optional<shared_ptr<T>> → optional<T>). *)
              let deref : Cpp_ir.Lowered.Expr.t = Dereference (Local binding_name) in
              (match field_ty with
               | Shared_pointer storage_inner when storage_inner <> bare_ty ->
                 Convert.gen_type_conversion_expr ~src_ty:storage_inner ~dst_ty:bare_ty deref
               | _ -> deref)
            else if field_ty <> bare_ty
                    && Convert.contains_shared_ptr field_ty then
              Convert.gen_type_conversion_expr ~src_ty:field_ty ~dst_ty:bare_ty
                (Cpp_ir.Expr.Local binding_name)
            else if field_is_wholesale_erased i
                    && not (Types.resolves_to_any_type cx bare_ty) then
              (* [resolves_to_any_type] (not just [prints_as_any]) so that a
                 field whose declared type is itself an erased alias (e.g.
                 [symbol_semty = std::any]) is NOT wrapped in a spurious
                 [any_cast<symbol_semty>]: the binding already holds the erased
                 value directly, and casting a [std::any] holding a container to
                 [std::any] would throw at runtime.  Only genuinely concrete
                 target types are unwrapped here. *)
              (match Convert.strip_ns_global_app bare_ty with
               | Entity_application (g, [_], _) when is_list_global g && not (Base.Table.is_custom g) ->
                 let list_any_ty : Cpp_ir.Lowered.Type.t =
                   match bare_ty with
                   | In_namespace (ns_g, _) -> In_namespace (ns_g, Entity_application (g, [Any], []))
                   | _ -> Entity_application (g, [Any], [])
                 in
                 Cpp_passes.Erasure.converting_ctor bare_ty [Cpp_passes.Erasure.unbox list_any_ty (Cpp_ir.Expr.Local binding_name)]
               | Entity_application (g, [elem_ty], _) when Base.Type_util.is_custom_list_global g ->
                 let erased_elem = Cpp_passes.Erasure.erase_type_to_any elem_ty in
                 let cast_ty : Cpp_ir.Lowered.Type.t =
                   if erased_elem = Any then bare_ty
                   else Entity_application (g, [erased_elem], [])
                 in
                 Cpp_passes.Erasure.unbox cast_ty (Cpp_ir.Expr.Local binding_name)
               | _ -> Cpp_passes.Erasure.unbox bare_ty (Cpp_ir.Expr.Local binding_name))
            else
              Local binding_name
          in
          List.map (fun st -> Lifting.local_var_subst_stmt ~keep_cast:true var_name subst_expr st) stmts
        else
          stmts )
      body_stmts
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let uptr_value_bindings =
    List.filter_map
      (fun (i, (_var_name, core_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, read, _, _) =
            field_bindings_arr.(i)
          in
          let is_uptr_field = read = Read_through_pointer in
          if is_uptr_field && branch_needs_sptr_preextract then
            let bare_ty =
              Types.cpp_of_core cx env core_ty
            in
            let value_id =
              Id.of_string (Id.to_string binding_name ^ "_value")
            in
            (* Bind as [const T& a_value = *a] rather than [T a_value = *a].
               [=] capture of a ref-typed local copies the referenced object
               into the closure (same semantics, no intermediate copy).
               [&] capture is safe because shared_ptr pre-extracts only occur
               inside non-escaping lambda scopes.
               When the stored type (storage_inner) differs from bare_ty,
               apply a conversion (e.g. optional<shared_ptr<T>> → optional<T>). *)
            let deref : Cpp_ir.Lowered.Expr.t = Dereference (Local binding_name) in
            let (_, field_ty', _, _, binder) = field_bindings_arr.(i) in
            let rhs =
              match field_ty' with
              | Shared_pointer storage_inner when storage_inner <> bare_ty ->
                Convert.gen_type_conversion_expr ~src_ty:storage_inner ~dst_ty:bare_ty deref
              | _ -> deref
            in
            (* The value is what the branch body reads for the pattern
               variable, so it stands for that variable's binder. *)
            Some
              (Bind_variable
                 ( value_id,
                   Declare (Reference (Lvalue, Const bare_ty), binder),
                   rhs ) : Cpp_ir.Lowered.Stmt.t)
          else None
        else None)
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let body_stmts = uptr_value_bindings @ body_stmts in
  (* Use std::get (smb_var = Some) when any constructor field is actually used;
     otherwise use holds_alternative only (smb_var = None). *)
  let has_used_fields = List.exists Fun.id dummies in
  { ctor_type = ctor_type;
    var = (if has_used_fields then Some sname else None);
    field_bindings =
      (if has_used_fields then
         List.map
           (fun (n, ty, _read, used, binder) : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Match.field_binding ->
             {name = n; type_ = ty; used = used; binder = binder})
           field_bindings
       else []);
    extra_conditions = [];
    body = body_stmts }

(** The match of [t] at [typ] with branches [pv] (the match [case_occ]), in
    expression position, as an immediately invoked lambda.

    Dispatches based on the inductive's structure:
    - {b Enum types}: a [Switch] statement on the tag.
    - {b Variant types}: a [Match] statement, an if/else-if chain using
      [std::holds_alternative] guards and [std::get] structured bindings
      ({!gen_match_branch}), with a Perceus reuse path where the plan
      rebuilds a constructor in the cell the match frees.  A flat
      single-constructor inductive is bound directly, with no variant
      access.

    {b Type resolution.}  The match type is first refined from the type of
    the variable the scrutinee reads ({!Match_types.match_scrutinee_type}), so that
    field types and constructor type parameters are concrete. *)
let rec gen_cpp_case cx ?slot (typ : Core.Type.t) t env pv case_occ : Cpp_ir.Lowered.Expr.t =
  (* A match that may reuse its cell generates each branch body in a reuse
     arm, under the arm's plan, and again in the shared arm. *)
  if Base.Table.reuse_here () && Lowering_state.matches_reuse cx then
    Ownership_ir.Region.Frame_save.generating_alternatives (fun () -> gen_cpp_case_once cx ?slot typ t env pv case_occ)
  else gen_cpp_case_once cx ?slot typ t env pv case_occ

and gen_cpp_case_once cx ?slot (typ : Core.Type.t) t env pv case_occ : Cpp_ir.Lowered.Expr.t =
  let typ =
    let var_type i = try Some (get_env_type cx i) with _ -> None in
    let at bt = Match_types.match_scrutinee_type cx env typ t pv ~var_type ~var_cpp_type:(fun _ -> bt) in
    (* Asked only of the variable the scrutinee reads; the binder's type
       matters only through the match type it gives. *)
    let read =
      match t with
      | Core.Expr.Bound_variable {occurrence = occ; _}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {occurrence = occ; _}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {occurrence = occ; _}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {occurrence = occ; _}; _} -> Some occ
      | _ -> None
    in
    Match_types.match_scrutinee_type cx env typ t pv ~var_type
      ~var_cpp_type:(fun i ->
        Option.bind read (fun occ ->
            Binders.planned_binder_type cx ~use:"scrutinee" ~agree:(fun p l -> at p = at l) i occ ))
  in
  let scrut_is_wrapped_case =
    match t with Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _ -> true | _ -> false in
  (* Check if this is an enum inductive type *)
  let is_enum =
    match typ with
    | Core.Type.Global_app {head = GlobRef.IndRef (kn, i); _} ->
      is_enum_inductive (GlobRef.IndRef (kn, i))
    | _ -> false
  in
  (* Check if this is a flat single-constructor inductive type *)
  let is_flat_match =
    match typ with
    | Core.Type.Global_app {head = r; _} -> Base.Table.is_flat_inductive r
    | _ -> false
  in
  if is_enum then (* Generate switch-based matching wrapped in IIFE *)
    let ind_ref =
      match typ with
      | Core.Type.Global_app {head = r; _} -> r
      | _ ->
        CErrors.anomaly (Pp.str "gen_case_cpp: enum type expected to be a Global_app")
    in
    let scrutinee =
      Match_types.recover_erased_scrutinee cx env ~is_magic:scrut_is_wrapped_case typ (gen_expr cx env t)
    in
    let rec gen_enum_branches = function
      | [] -> []
      | {Core.Match.Branch.binders = ids; pattern = p; body = body; _} :: cs ->
      match p with
      | Core.Pattern.Constructor {constructor = r; _} ->
        let ids', env' =
          push_vars'
            (List.rev_map
               (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty))
               ids )
            env
        in
        let ctor_name =
          match r with
          | GlobRef.ConstructRef ((kn, i), cidx) ->
            Id.of_string (Base.Common.enum_ctor_name_of_ref kn i cidx)
          | _ -> Id.of_string (Base.Common.enum_ctor_name_of_id
                   (Base.Table.safe_basename_of_global r))
        in
        let body_stmts =
          Binders.with_binders cx env ids' (fun () ->
              gen_stmts cx ?slot env' (Destination.return_ cx) body )
        in
        (ctor_name, body_stmts) :: gen_enum_branches cs
      | Core.Pattern.Wildcard | Core.Pattern.Bound_variable _ | Core.Pattern.Tuple _ -> gen_enum_branches cs
    in
    let gen_default_stmts () =
      let wild_br =
        Array.to_list pv
        |> List.find_opt
          (fun {Core.Match.Branch.pattern = p; _} -> match p with Core.Pattern.Wildcard -> true | _ -> false)
      in
      Option.map
        (fun (br : Core.Match.Branch.t) -> gen_stmts cx ?slot:(branch_slot ?slot br.result_type) env (Destination.return_ cx) br.body)
        wild_br
    in
    let void_ret = Match_types.iife_void_return cx env typ pv in
    let branches, default =
      let ret =
        match void_ret with
        | Some Void -> void_ret
        | _ -> current_cpp_return_type cx ()
      in
      with_cpp_return_type cx ret (fun () ->
          let branches = gen_enum_branches (Array.to_list pv) in
          (branches, gen_default_stmts ()) )
    in
    let body : Cpp_ir.Lowered.Stmt.t list =
      [Switch {scrutinee = scrutinee; enum = ind_ref; branches = branches; default = default}]
    in
    let iife_ret_opt =
      match void_ret with
      | Some _ -> Some Cpp_ir.Type.Void
      | None ->
        Match_types.iife_closure_return ?ret:(current_cpp_return_type cx ()) cx env typ pv body
    in
    Cpp_ir.Build.iife iife_ret_opt body
  else
    (* Generate if/else-if pattern matching using [std::holds_alternative]
       and [std::get].  Produces a [Match] statement wrapped in an IIFE. *)
    let scrut_db = Match_types.scrutinee_binder cx t in
    (* Allocate a unique [_m] name for this match level.  All branches of
       the same match reuse this name (each [if (auto* _m = ...)] creates
       its own scope); nested matches get the next name ([_m0], [_m1]). *)
    let match_i = cx.ctx.threaded.match_param_counter in
    set_threaded cx (fun t -> { t with match_param_counter = match_i + 1 });
    let sname =
      Id.of_string
        ( if match_i = 0 then "_m"
          else "_m" ^ string_of_int (match_i - 1) )
    in
    (* The scrutinee is referenced across all branches, so the plan has a
       read of it as one in place, never moved ({!Ownership_ir.Region.Inspected}). *)
    let scrut_expr = gen_expr cx env t in
    let scrut_expr =
      Match_types.recover_erased_scrutinee cx env ~is_magic:scrut_is_wrapped_case typ scrut_expr
    in
    (* A shared variant is matched by reading: a field taken out of it is a
       count bump, while decomposing it through [v_mut()] would first copy a
       block anyone else holds. *)
    let scrut_is_shared =
      match typ with Core.Type.Global_app {head = r; _} -> Base.Table.is_shared_variant r | _ -> false
    in
    (* Whether this match may consume the scrutinee.  A shared value is
       matched by borrowing all the same -- its fields are count bumps away --
       and is consumed only by block reuse below. *)
    let scrut_consumable = Ownership_ir.Region.owns_scrutinee cx.ctx.lexical.move_plan t in
    let scrut_is_owned = scrut_consumable && not scrut_is_shared in
    (* Build variant accessor.  All inductives (including coinductives)
       are value types and use [scrut.v()] (dot access).  Exception:
       [this] is always a pointer, so method bodies use [this->v()].
       For flat types (no variant wrapper), use the scrutinee directly. *)
    let scrut_is_ptr =
      match scrut_expr with This -> true | _ -> false
    in
    let scrut_v : Cpp_ir.Lowered.Expr.t =
      if is_flat_match then
        scrut_expr
      else if scrut_is_ptr then
        Access_call (Arrow, scrut_expr, Id.of_string "v", [])
      else
        Cpp_ir.Build.call (Access (Dot, scrut_expr, Id.of_string "v")) []
    in
    let scrut : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Match.scrutinee =
      { expr = scrut_v;
        access = Dot;
        owned = scrut_is_owned;
        flat = is_flat_match }
    in
    (* Push renamed pattern variables into the environment, register their
       types in [env_types], and compute a dummies mask (true = non-Dummy).
       The caller is responsible for saving/restoring env_types. *)
    let process_match_pattern_vars ids env =
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty))
             ids )
          env
      in
      let env_ids' = Match_types.retype_dependent_params typ ids' in
      Binders.push_binders cx env env_ids';
      let dummies =
        List.map (fun (x, _) -> match x with Core.Binder_name.Anonymous -> false | _ -> true) ids
      in
      (ids', env', dummies)
    in
    (* Generate one [Match.branch] per constructor pattern, collecting
       a wildcard body from [Core.Pattern.Wildcard] / [Core.Pattern.Bound_variable]. *)
    let rec gen_branches i = function
      | [] -> ([], None)
      | {Core.Match.Branch.binders = ids; result_type = rty; pattern = p; body = body} :: cs ->
      match p with
      | Core.Pattern.Constructor {constructor = r; _} ->
        let saved_env_types = cx.ctx.lexical.env_types in
        let saved_erased = Binders.save_erased_env cx () in
        let ids', env', dummies = process_match_pattern_vars ids env in
        let br =
          gen_match_branch cx ?slot env' typ rty r ids' dummies body sname
            match_i scrut ~scrut_db ~site:(Branch (case_occ, i))
        in
        restore_env_types cx saved_env_types;
        Binders.restore_erased_env cx saved_erased;
        let rest, wild = gen_branches (i + 1) cs in
        (br :: rest, wild)
      | Core.Pattern.Wildcard | Core.Pattern.Bound_variable _ ->
        let body_stmts =
          gen_stmts cx ?slot:(branch_slot ?slot rty) env (Destination.return_ cx) body
        in
        ([], Some body_stmts)
      | Core.Pattern.Tuple _ -> gen_branches (i + 1) cs
    in
    let branches, wildcard = gen_branches 0 (Array.to_list pv) in
    let iife_ret_opt =
      match Match_types.iife_void_return cx env typ pv with
      | Some _ -> Some Cpp_ir.Type.Void
      | None ->
        (* The branches were written under [branch_return] of the return
           type in force (see {!gen_match_branch}). *)
        let ret =
          match (current_cpp_return_type cx (), Array.to_list pv) with
          | Some Void, _ | _, [] -> None
          | rt, {Core.Match.Branch.result_type = rty; _} :: _ -> branch_return cx env rt rty
        in
        Match_types.iife_closure_return ?ret cx env typ pv [Match (scrut, branches, wildcard)]
    in
    (* Perceus reuse (Crane Reuse): rebuild a same-inductive constructor in
       a cell the match frees instead of allocating, via the [<ctor>__reuse]
       factory.  Dual path guarded by [scrut.v().index()==branch_idx] and a
       uniqueness test; otherwise the normal [Match].  Which cell:
       - a shared variant: the scrutinee's own block, when no other value
         holds it -- the fields are moved out, and the factory writes the new
         ones in (or allocates, if the rebuilt constructor is another);
       - otherwise, under NonAtomicRc (crane::rc carries the reusable control
         block): the matched constructor's first recursive child's cell, when
         unique -- a map's node has two, and its rebuild recycles the first.
       Only for an owned, non-coinductive scrutinee. *)
    let reuse_stmts_opt =
      if Base.Table.reuse_here () && Lowering_state.matches_reuse cx
         && (if scrut_is_shared then scrut_consumable
             else Lowering_state.non_atomic_rc cx && scrut_is_owned)
         && (not is_flat_match) && (not is_enum)
         && (match typ with Core.Type.Global_app {head = r; _} -> not (Base.Table.is_coinductive r) | _ -> true)
      then
        let scrut_cpp_ty = Types.cpp_of_core cx env typ in
        (* The recycled cell is a [crane::rc] over the *scrutinee's* inductive
           instance, so it can only be handed to a [__reuse] factory that
           rebuilds that same instance.  A type-changing function such as
           [mapl : (A -> B) -> lst A -> lst B] matches on [lst A] but rebuilds
           [lst B]: the two differ in size, alignment and destructor, so
           recycling the cell is not merely a type error but unsound.  Require
           the branch to reconstruct exactly the scrutinee's type. *)
        let branch_rebuilds_scrut_ty branch_idx =
          let {Core.Match.Branch.result_type = rty; _} = pv.(branch_idx) in
          Base.Type_util.cpp_ty_eq scrut_cpp_ty
            (Types.cpp_of_core cx env rty)
        in
        (* The arm moves the scrutinee's fields out and recycles its child's
           cell, so a body that reads the scrutinee whole -- an association
           list's [add] returning [(k, x) :: s] -- would read what is left. *)
        let body_reads_scrutinee branch_idx =
          let {Core.Match.Branch.binders = ids; body = body; _} = pv.(branch_idx) in
          match scrut_db with
          | Some db -> Base.Core_util.ast_occurs (db + List.length ids) body
          | None -> false
        in
        let try_cand (branch_idx, matched_ctor, _ar, tail_ctor, _ta) =
          if not (branch_rebuilds_scrut_ty branch_idx) then None
          else if body_reads_scrutinee branch_idx then None
          else
          let {Core.Match.Branch.binders = ids; body = body; _} = pv.(branch_idx) in
          let ids', env' =
            push_vars'
              (List.rev_map
                 (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty))
                 ids)
              env
          in
          let rev_ids' = List.rev ids' in
          let dummies_arr =
            Array.of_list (List.map (fun (x, _) -> match x with Core.Binder_name.Anonymous -> false | _ -> true) ids)
          in
          (* How each bound field comes out of the recycled node, read off
             the constructor's own field types: the token -- the first field
             holding the scrutinee's inductive itself, uniformly -- has its
             value moved out of its cell; another field behind a pointer, or
             in a [crane::field], is copied, since only the token's cell was
             found unique; a field stored in place is moved.  A field the
             rules do not cover -- a self-reference inside a container, a
             mutual sibling -- declines reuse. *)
          let def_tys =
            match Base.Table.get_ctor_ip_types_opt matched_ctor with
            | Some tys -> List.filter (fun t -> not (is_erased_type t)) tys
            | None -> []
          in
          let self_ref =
            match typ with Core.Type.Global_app {head = (GlobRef.IndRef _ as r); _} -> Some r | _ -> None
          in
          let is_uniform_self t =
            match (Base.Core_util.core_resolve t, self_ref) with
            | Core.Type.Global_app {head = r; type_arguments = args; _}, Some r0 when GlobRef.CanOrd.equal r r0 ->
              List.for_all Fun.id
                (List.mapi
                   (fun j a ->
                     match Base.Core_util.core_resolve a with
                     | Core.Type.Variable {variable = k; _} -> k = j + 1
                     | _ -> false )
                   args )
            | _ -> false
          in
          let rec mentions_family t =
            match (Base.Core_util.core_resolve t, self_ref) with
            | Core.Type.Global_app {head = GlobRef.IndRef (kn, _); _}, Some (GlobRef.IndRef (kn0, _))
              when MutInd.CanOrd.equal kn kn0 ->
              true
            | Core.Type.Global_app {type_arguments = args; _}, _ -> List.exists mentions_family args
            | Core.Type.Arrow {parameter = a; result = b}, _ -> mentions_family a || mentions_family b
            | _ -> false
          in
          let reads =
            List.mapi
              (fun i _ ->
                if not dummies_arr.(i) then Some `Unused
                else
                  match List.nth_opt def_tys i with
                  | Some t when is_uniform_self t -> Some `Child
                  | Some t when Base.Type_util.boxes_field t -> Some `Deref
                  | Some t
                    when Base.Type_util.boxes_param_field
                           ~owner:(match matched_ctor with
                                   | GlobRef.ConstructRef (ind, _) -> GlobRef.IndRef ind
                                   | r -> r)
                           t -> Some `Unbox
                  | Some t when mentions_family t -> None
                  | Some _ -> Some `Move
                  | None -> None )
              rev_ids'
          in
          (* The constructor rebuilt must have somewhere to put the cell: a
             shared variant's block needs fields to hold, a child's cell needs
             a field holding the inductive itself.  [nil] has neither. *)
          let tail_tys =
            Option.default [] (Base.Table.get_ctor_ip_types_opt tail_ctor)
          in
          let reused_cell =
            if List.mem None reads then None
            else if scrut_is_shared then
              if def_tys <> [] && List.exists (fun t -> not (is_erased_type t)) tail_tys
              then Some `Block
              else None
            else if not (List.exists is_uniform_self tail_tys) then None
            else
              let rec first i = function
                | Some `Child :: _ -> Some (`Child_cell i)
                | _ :: rest -> first (i + 1) rest
                | [] -> None
              in
              first 0 reads
          in
          (match reused_cell with
          | Some reused_cell ->
            let saved_env_types = cx.ctx.lexical.env_types in
            Binders.push_binders cx env ids';
            if Base.Probe.checking () then
              List.iteri
                (fun i _ ->
                  Representation_plan.check ~as_bound:true cx.ctx ~site:(Branch (case_occ, branch_idx)) ~field:i
                    ~live:(Binders.binder_is_boxed cx (List.length ids' - i)) () )
                rev_ids';
            let scrut_vmut : Cpp_ir.Lowered.Expr.t =
              if scrut_is_ptr then
                Access_call (Arrow, scrut_expr, Id.of_string "v_mut", [])
              else
                Cpp_ir.Build.call (Access (Dot, scrut_expr, Id.of_string "v_mut")) []
            in
            (* Name the alternative rather than number it: the branch index
               and the variant position coincide, but [std::get<typename
               T::Ctor>] says which constructor is being reused. *)
            let matched_alt =
              Id.of_string_soft (ctor_struct_name_of_ref matched_ctor)
            in
            (* The field by the name the constructor's struct gives it --
               [l] for [list]'s tail, not the positional [a1]. *)
            let rf i : Cpp_ir.Lowered.Expr.t =
              Access
                ( Dot,
                  Variant_get (Member (scrut_cpp_ty, matched_alt), Some scrut_vmut),
                  Base.Common.lookup_ctor_field_name ~owner:matched_ctor
                    (ctor_struct_name_of_ref matched_ctor) i )
            in
            (* A field moved out: the token's cell keeps nothing the arm
               reads.  In a unique block every child is the block's alone. *)
            let moved_child i =
              match reused_cell with
              | `Block -> true
              | `Child_cell k -> i = k
            in
            let extract =
              List.concat
                (List.map2
                   (fun (i, (var_name, core_ty)) read ->
                     let binder = local_binder cx ~site:(Branch (case_occ, branch_idx)) env' var_name in
                     let bind e : Cpp_ir.Lowered.Stmt.t list =
                       [Bind_variable (var_name, Declare (Types.cpp_of_core cx env core_ty, binder), e)]
                     in
                     match read with
                     | Some `Unused | None -> []
                     (* The token: its value is moved out, owned, so the
                        recursion propagates reuse; the cell stays behind as
                        the token. *)
                     | Some `Child when moved_child i -> bind (Move (Dereference (rf i)))
                     | Some (`Child | `Deref) -> bind (Dereference (rf i))
                     | Some `Unbox -> bind (Cpp_ir.Build.call (Runtime Cpp_ir.Crane_rt.Unbox_field) [rf i])
                     | Some `Move -> bind (Move (rf i)) )
                   (List.mapi (fun i x -> (i, x)) rev_ids')
                   reads)
            in
            let tok, (unique_cond : Cpp_ir.Lowered.Expr.t) =
              match reused_cell with
              | `Block ->
                (scrut_expr, Cpp_ir.Build.call (Access (Dot, scrut_v, Id.of_string "unique")) [])
              | `Child_cell k ->
                ( rf k,
                  Binary
                    ( Equal,
                      Cpp_ir.Build.call (Access (Dot, rf k, Id.of_string "use_count")) [],
                      Literal (Int 1) ) )
            in
            (* Every field the arm binds is a local of its own, owned: the
               plan of the arm says so. *)
            let body_stmts =
              with_reuse_token cx (Some tok) (fun () ->
                  with_plan cx
                    (Ownership_ir.Region.reuse_arm cx.ctx.lexical.move_plan ~scrutinee:t ~branch:branch_idx
                       ~constructor:tail_ctor)
                    (fun () -> gen_stmts cx ?slot env' (Destination.return_ cx) body) )
            in
            restore_env_types cx saved_env_types;
            Some (branch_idx, extract @ body_stmts, unique_cond)
          | _ -> None )
        in
        (* Pick the first candidate whose matched constructor has a recursive
           field (skips nullary-reconstruction arms like Nil->Nil that have no
           cell to recycle). *)
        List.find_map try_cand (Core_plan.Escape.find_reuse_candidates pv)
      else None
    in
    ( match reuse_stmts_opt with
    | Some (branch_idx, reuse_body, use_count_cond) ->
      let index_cond : Cpp_ir.Lowered.Expr.t =
        Binary
          ( Equal,
            Cpp_ir.Build.call (Access (Dot, scrut_v, Id.of_string "index")) [],
            Literal (Int branch_idx) )
      in
      let normal : Cpp_ir.Lowered.Stmt.t list = [Match (scrut, branches, wildcard)] in
      Cpp_ir.Build.iife iife_ret_opt
        [ Comment "Reuse the matched cell in place when this is its only owner; otherwise rebuild.";
          If
            { condition = index_cond;
              then_ = [If {condition = use_count_cond; then_ = reuse_body; else_ = normal}];
              else_ = normal } ]
    | None ->
      Cpp_ir.Build.iife iife_ret_opt [Match (scrut, branches, wildcard)] )

(** One branch of a custom match: its parameters [ids] typed for the
    template (a self-reference of the scrutinee's inductive [scrut_ind_opt]
    spelled as the struct stores it), its C++ return type from [rty], and
    [body] as statements ending in [k], an erased variable returned at a
    template-parameter type unboxed first.  [site] is the branch, binding
    [ids]. *)
let gen_cpp_custom_body cx ?slot env (k : Destination.t) rty ids body scrut_ind_opt ~site =
  let tvars = get_current_type_vars cx in
  let ret = Types.cpp_of_core cx env rty in
  let n_pat_vars = List.length ids in
  let ids =
    List.mapi
      (fun j (x, ty) ->
        if Base.Probe.checking ()
           && not (Option.equal Id.equal (get_db_name_opt (n_pat_vars - j) env) (Some x))
        then
          Base.Probe.violation "custom match binder"
            Pp.(str "parameter " ++ int j ++ str " is not " ++ Id.print x ++ str " in its branch's scope");
        let ns =
          match scrut_ind_opt with
          | Some g_scrut when not (is_prod_global g_scrut) ->
            (* Use {g_scrut} as the namespace so that type args that are
               self-references of the scrutinee get shared_ptr wrapping —
               matching struct field storage.  Exception 1: a product's
               components are bound at the bare type, as a field holding a
               nested self-reference stores it (see [field_storage_ty]): the
               field is boxed whole, so [(nat * option tree)] holds an
               [std::optional<tree>].  Exception 2: when the binding type IS
               g_scrut directly (a non-parametric direct self-ref
               dereferenced by the custom match template), use empty ns so
               the binding is a value type rather than shared_ptr. *)
            let is_direct_self_ref =
              match ty with
              | Core.Type.Global_app {head = g; type_arguments = []; _} -> GlobRef.CanOrd.equal g g_scrut
              | _ -> false
            in
            if is_direct_self_ref then Core.Ref.User.Set.empty
            else Core.Ref.User.Set.singleton g_scrut
          | _ -> Core.Ref.User.Set.empty
        in
        ( { name = x;
            type_ = Types.cpp_ir_of_core_type cx env ~ns tvars ty;
            binder = core_binder cx ~site env (n_pat_vars - j) }
          : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Custom_match.param ) )
      (List.rev ids)
  in
  (* Wrap erased variables with any_cast when returned as a template parameter. *)
  let k =
    match ret with
    | Variable _ ->
      let body_is_erased =
        match body with
        | Core.Expr.Bound_variable {index = i; occurrence = occ}
        | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _}
        | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _}
        | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _} ->
          not (Binders.read_is_boxed cx i occ) && Erasure.is_env_var_erased cx env tvars i
        | _ -> false
      in
      if body_is_erased then Destination.adapted (Cpp_passes.Erasure.unbox ret) k
      else k
    | _ -> k
  in
  let body = gen_stmts cx ?slot:(branch_slot ?slot rty) env k body in
  (ids, ret, body)

(** Generate a custom case expression using user-provided extraction syntax.
    Entry point for custom pattern match generation.
    Returns statements: when the scrutinee is non-trivial and the
    template uses [%scrut] more than once, a cache declaration
    [auto _cs = expr;] is prepended before the [Custom_match] statement. *)
let gen_custom_cpp_case cx ?slot env (k : Destination.t) (typ : Core.Type.t) t pv case_occ :
    Cpp_ir.Lowered.Stmt.t list =
  (* Save the Core type for temps computation after fix_a_fired is known. *)
  let core_typ = typ in
  let cs =
    Match_types.custom_match_scrutinee cx env typ t pv ~var_boxed:(Binders.read_is_boxed cx)
      ~var_type:(get_env_type_opt cx)
  in
  let scrut_is_wrapped = cs.Match_types.wrapped in
  let scrut_is_cpp_erased = cs.Match_types.cpp_erased in
  let scrut_is_magic = cs.Match_types.magic in
  let typ = cs.Match_types.typ in
  let concrete_match_type = cs.Match_types.concrete in
  (* Custom match templates may use %scrut multiple times (e.g., option: "if
     (%scrut.has_value()) { ... *%scrut; ... }"). Each occurrence re-prints the
     scrutinee C++ expression: a variable is then read in place (the plan has
     no move of it, {!Ownership_ir.Region.Inspected}), and anything else is bound
     once to a temporary below. *)
  let cmatch = find_custom_match pv in
  let scrut_uses =
    List.length
      (List.filter (( = ) Cpp_ir.Foreign_template.Scrut) (Cpp_ir.Foreign_template.match_template cmatch))
  in
  (* Whether the match binds the pair's components by value, moving them out:
     asked while [t] is still the Core scrutinee. *)
  let pair_by_value = Ownership_ir.Region.pair_by_value cx.ctx.lexical.move_plan t pv in
  (* A scrutinee whose result is only pinned down by a type index arrives
     boxed, and a match cannot inspect a [std::any].  Telling the call what
     type this position wants is what makes it recover the value. *)
  (* The scrutinee's binder, resolved while [t] is still the Core scrutinee:
     below it is rebound to the generated C++ expression, and inside
     [gen_cases] the name belongs to a branch body. *)
  let scrut_db = Match_types.scrutinee_binder cx t in
  let typ_ir = typ in
  let scrut_expected =
    match Match_types.flatten_app t with
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; _}
      when (match find_type_opt r with
            | Some fty -> result_is_index_only_tvar fty
            | None -> false) -> Some typ_ir
    | _ -> None
  in
  (* A scrutinee is not a tail position: whatever the enclosing function
     returns says nothing about the value being matched on.  Naming the
     match's own type here keeps {!Coerce.position_cpp_ty}'s fallback from recovering a
     boxed scrutinee at the return type -- [any_cast<step_result>] on what is
     a [bool]. *)
  let t =
    let saved_ret = cx.ctx.lexical.current_cpp_return_type in
    set_lexical cx (fun l -> { l with current_cpp_return_type = Some typ_ir });
    let t = gen_expr cx ?expected_ty:scrut_expected env t in
    set_lexical cx (fun l -> { l with current_cpp_return_type = saved_ret });
    t
  in
  let pair_g_opt = cs.Match_types.pair in
  (* Insert [any_cast] on the scrutinee when the runtime value is [std::any]
     but the template needs a typed expression.

     For pair matches: the runtime encoding is always [pair<any,any>] at every
     nesting level (built by [concat_tuple]/[rev_tuple_cons_case]).  Cast to
     [pair<any,any>] regardless of the static type and set [fix_a_fired=true]
     so downstream passes know the fields are [std::any].

     For non-pair matches (option, variant, etc.) when [scrut_is_magic]: cast
     to [concrete_match_type] recovered from the branch pattern.

     Otherwise: no cast needed; the scrutinee already has the correct type. *)
  let t, fix_a_fired, cast_to =
    let needs_pair_any_cast = cs.Match_types.pair_any_cast in
    if needs_pair_any_cast then begin
      let g = Option.get pair_g_opt in
      (Cpp_passes.Erasure.unbox (Entity_application (g, [Any; Any], [])) t, true, None)
    end
    else if (scrut_is_wrapped || (scrut_is_magic && Cpp_ir.Types.prints_as_any typ)
             || scrut_is_cpp_erased)
            && not (Cpp_ir.Types.prints_as_any concrete_match_type) then
      (* Erase template args one level deep, preserving nested generic structure.
         E.g., deque<pair<T1,T2>> → deque<pair<any,any>>, deque<T> → deque<any>. *)
      let erase_tparams : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
        | Entity_application (_, [], _) -> Any
        | Entity_application (g2, args2, ns2) -> Entity_application (g2, List.map (fun _ -> Cpp_ir.Type.Any) args2, ns2)
        | _ -> Any
      in
      (* Canonical erased shape for a LIST scrutinee is [deque<std::any>] -- a
         bare [std::any] per element -- not a structure-preserving
         [deque<pair<any,any>>]: a sibling producer for the same Coq list type
         (e.g. a base-case action erasing an empty list) may already have
         erased to the flat shape, and casting this scrutinee to the
         structure-preserving shape instead would throw [std::bad_any_cast]
         at runtime.  See the matching invariant in [gen_expr]'s
         [Core.Expr.Bound_variable]/[Core.Expr.Coerce] cases. *)
      let cast_ty : Cpp_ir.Lowered.Type.t = match concrete_match_type with
        | Entity_application (g, (_ :: _), ns) when is_list_global g ->
          Entity_application (g, [Any], ns)
        | Entity_application (g, (_ :: _ as args), ns) when scrut_is_wrapped ->
          Entity_application (g, List.map erase_tparams args, ns)
        | _ -> concrete_match_type
      in
      (Cpp_passes.Erasure.unbox cast_ty t, false, Some cast_ty)
    else
      (t, false, None)
  in
  (* When [fix_a_fired], pass [pair<any,any>] as the [Custom_match] type so
     that {!Cpp_passes.Erasure.lower_boxed_reads} reads the scrutinee at
     [pair<any,any>] instead of the concrete nested pair type. *)
  let case_typ : Cpp_ir.Lowered.Type.t =
    if fix_a_fired then
      match pair_g_opt with
      | Some g -> Entity_application (g, [Any; Any], [])
      | None -> typ
    else
      (* The scrutinee is read at the type it was cast to, which is what a
         template naming its type ([%ty]) has to say. *)
      match cast_to with Some ty -> ty | None -> typ
  in
  (* Compute template type parameters ([%t0], [%t1], ...) after [fix_a_fired]
     is known.  When [fix_a_fired], the scrutinee is cast to [pair<any,any>],
     so all fields are [std::any] regardless of the original field types.
     Force [Auto] so the binding uses [auto] and C++ deduces the type.
     Also force [Auto] when a type contains erased positions ([Any]),
     since an explicit type annotation would block valid concrete-type calls,
     and when the scrutinee is read at an erased instantiation (cast to
     [std::deque<crane::obj>]): its elements are not of the Core types. *)
  let erased_cast = match cast_to with Some ty -> has_tany_in_type ty | None -> false in
  let temps =
    match core_typ with
    | Core.Type.Global_app {type_arguments = tys; _} ->
      let raw = Types.template_params_of_core cx ~site:Cpp_ir.Types.Declared env tys in
      List.map (fun ty : Cpp_ir.Lowered.Type.t ->
        if fix_a_fired || erased_cast || has_tany_in_type ty then Auto else ty) raw
    | _ -> []
  in
  (* When the template uses %scrut more than once and the scrutinee is a
     non-trivial expression (function call, constructor, etc.), cache it in
     a temporary to avoid double evaluation. *)
  let scrut, cache_prefix =
    if scrut_uses > 1 && not (Match_types.is_trivial_scrut t) then begin
      let n = cx.ctx.threaded.cs_counter in
      set_threaded cx (fun t -> { t with cs_counter = n + 1 });
      let cache_id = Base.Common.scrutinee_cache_id n in
      match Cpp_build.lift_iife_assignment cache_id None t with
      | Some stmts -> (Cpp_ir.Expr.Local cache_id, stmts)
      | None ->
        (Cpp_ir.Expr.Local cache_id, [(Bind_variable (cache_id, Declare (Auto, None), t) : Cpp_ir.Lowered.Stmt.t)])
    end else begin
      (t, [])
    end
  in
  (* Generate [(params, ret_ty, body)] triples for each branch.  Handles env
     retyping for [fix_a_fired], use-site
     [any_cast] insertion, and template-arg stripping for erased arguments. *)
  let rec gen_cases i = function
    | [] -> []
    | {Core.Match.Branch.binders = ids; result_type = rty; pattern = p; body = t} :: cs ->
    match p with
    | Core.Pattern.Constructor {constructor = r; _} ->
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty))
             ids )
          env
      in
      (* When [fix_a_fired], all pair fields are [std::any] at runtime.
         Variables whose C++ type is a pair (e.g. [pair<any,pair<any,…>>]) are
         also [std::any] — they came from [.second] of a [pair<any,any>].
         Re-type them as [Any] so that:
         (1) inner pair matches see an erased scrutinee and emit [any_cast],
         (2) {!Cpp_passes.Erasure.lower_boxed_reads} treats them as boxed.
         Non-pair leaf types (e.g. [List<any>]) are left unchanged so the
         use-site [any_cast] pass can still insert the correct cast. *)
      let scrut_elems_are_any =
        (scrut_is_wrapped || scrut_is_magic)
        && (match core_typ with
            | Core.Type.Global_app {head = g;
                                    type_arguments = _ :: _; _} when Base.Type_util.is_custom_list_global g -> true
            | _ -> false)
      in
      (* The scrutinee binder's own type, where it is known and says more
         than the case's annotation. *)
      let scrut_core_typ =
        match scrut_db with
        | Some db -> (
          match get_env_type_opt cx db with
          | Some t when not (core_type_contains_erased t) -> t
          | _ -> core_typ )
        | None -> core_typ
      in
      let ids' = Match_types.custom_branch_binders cx env ~fix_a_fired ~scrut_core_typ ~core_typ r ids' in
      let n_pat_vars = List.length ids in
      let saved_env_types = cx.ctx.lexical.env_types in
      Binders.push_binders cx env ids';
      (* When [fix_a_fired] and the outer scrutinee was truly [pair<any,any>]
         at runtime (i.e. outer [typ] was erased, not just magic-wrapped),
         ALL fields are [std::any] at runtime.  Record them as boxed
         so that [gen_expr] emits [any_cast<T>] when they're used at concrete
         types, and so inner pair matches emit [any_cast<pair<any,any>>].
         Use original [ids] types (not the retyped [ids']) to detect field types. *)
      if fix_a_fired then begin
        List.iteri (fun field_i _ ->
          let db_idx = n_pat_vars - field_i in
          Binders.record_binder_type cx db_idx Cpp_ir.Type.Any)
          ids
      end;
      let non_erased_def_tys =
        let def_site_field_tys =
          match Base.Table.get_ctor_ip_types_opt r with
          | Some tys -> tys | None -> []
        in
        List.filter (fun t -> not (is_erased_type t)) def_site_field_tys
      in
      Match_types.populate_erased_field_env cx
        ?scrut_db:
          (Option.map (fun i -> i + n_pat_vars) scrut_db)
        ~cname:r ~typ:core_typ ~env ~n_pat_vars
        ~n_fields:(List.length ids)
        ~non_erased_def_site_field_tys:non_erased_def_tys ();
      if scrut_elems_are_any then begin
        let n_fields = List.length ids in
        List.iteri (fun field_i _ ->
          let is_self_ref =
            match List.nth_opt non_erased_def_tys field_i with
            | Some (Core.Type.Global_app {head = g; _}) -> is_list_global g
            | _ -> false
          in
          if not is_self_ref then begin
            let db_idx = n_pat_vars - field_i in
            Binders.record_binder_type cx db_idx Cpp_ir.Type.Any
          end)
          (List.init n_fields Fun.id)
      end;
      if Base.Probe.checking () then
        List.iteri
          (fun field_i _ ->
            Representation_plan.check cx.ctx ~site:(Branch (case_occ, i)) ~field:field_i
              ~live:(Binders.binder_is_boxed cx (n_pat_vars - field_i)) () )
          ids;
      let scrut_ind_opt =
        match core_typ with
        | Core.Type.Global_app {head = GlobRef.IndRef _ as g; _} -> Some g
        | _ -> None
      in
      let (br_ids, br_ret, br_stmts) =
        gen_cpp_custom_body cx ?slot env' k rty ids' t scrut_ind_opt ~site:(Branch (case_occ, i))
      in
      restore_env_types cx saved_env_types;
      (* Use-site [any_cast] insertion: when [fix_a_fired], pair fields are all
         [std::any] at the binding site.  Pattern variables whose C++ type is
         concrete need [any_cast<T>] at each use site so the body compiles.
         Special cases:
         - Pair-typed vars use [pair<any,any>] (not the static type) because
           the runtime encoding always nests [pair<any,any>].
         - List vars use a converting constructor [List<T>(any_cast<List<any>>)]
           so element types are cast correctly.
         - Opaque type aliases / qualified member types are passed through
           as-is (the stored value IS the payload, not wrapped in [any]). *)
      let br_stmts =
        if fix_a_fired then
          List.fold_left
            (fun stmts ({name = name; type_ = cpp_ty; _} : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Custom_match.param) ->
               if not (Cpp_ir.Types.prints_as_any cpp_ty) then
                 let stripped = Convert.strip_ns_global_app cpp_ty in
                 let cast_expr : Cpp_ir.Lowered.Expr.t =
                   match stripped with
                   | Entity_application (g, _, _) when is_prod_global g ->
                     Cpp_passes.Erasure.unbox (Entity_application (g, [Any; Any], [])) (Cpp_ir.Expr.Local name)
                   | Entity_application (g, [_], _) when is_list_global g && not (Base.Table.is_custom g) ->
                     (* List<T> is stored as List<any> by grammar productions —
                        use the converting constructor List<T>(any_cast<List<any>>(v))
                        so each element is any_cast'd correctly.
                        Preserve any In_namespace wrapper for correct rendering. *)
                     let list_any_ty : Cpp_ir.Lowered.Type.t =
                       match cpp_ty with
                       | In_namespace (ns_g, _) ->
                         In_namespace (ns_g, Entity_application (g, [Any], []))
                       | _ -> Entity_application (g, [Any], [])
                     in
                     Cpp_passes.Erasure.converting_ctor cpp_ty [Cpp_passes.Erasure.unbox list_any_ty (Cpp_ir.Expr.Local name)]
                   | Entity_application (g, [_], _) when Base.Type_util.is_custom_list_global g ->
                     Local name
                   | Member _ | Entity_application (GlobRef.ConstRef _, _, _) ->
                     (* Opaque type alias (e.g. nt_semty = std::any) or
                        qualified member type (e.g. typename Ty::sym_semty):
                        the stored value IS the concrete payload, NOT a std::any
                        wrapping it. any_cast<std::any>(any(V)) throws; pass
                        the std::any value as-is. *)
                     Local name
                   | _ -> Cpp_passes.Erasure.unbox cpp_ty (Cpp_ir.Expr.Local name)
                 in
                 List.map (fun st -> Lifting.local_var_subst_stmt ~keep_cast:true name cast_expr st) stmts
               else stmts)
            br_stmts
            br_ids
        else br_stmts
      in
      (* Strip explicit template type args from function calls where any
         argument has erased-type content (either wrapped in [any_cast<T>]
         with [Any] inside, or a pattern var whose C++ type contains [Any]).
         Lets C++ deduce the correct type from the argument itself instead of
         using a stale concrete annotation that conflicts with the erased
         runtime type. *)
      let br_stmts =
        let tany_pat_var_names =
          if not fix_a_fired then
            List.fold_left (fun acc (p : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Custom_match.param) ->
              if has_tany_in_type p.type_ then Id.Set.add p.name acc else acc)
              Id.Set.empty br_ids
          else Id.Set.empty
        in
        let should_strip args =
          List.exists (fun (a : Cpp_ir.Lowered.Expr.t) ->
            match a with
            | Any_cast (ty, _) -> has_tany_in_type ty
            | Local name -> Id.Set.mem name tany_pat_var_names
            | _ -> false) args
        in
        if fix_a_fired || not (Id.Set.is_empty tany_pat_var_names) then
          (* Deduction is what this pass falls back on, so it may only give
             up an argument deduction could have recovered.  A type
             constructor is the one thing it cannot: the carrier occupies a
             non-deduced position, which is why it was written out in the
             first place, and an erased argument is the very case that made
             it unrecoverable.  Stripping it hands the call to a deduction
             that reads through the alias to its body and answers with the
             wrong constructor. *)
          let recovered_carrier tys =
            List.exists (fun (t : Cpp_ir.Lowered.Type.t) -> match t with Type_constructor _ -> true | _ -> false) tys
          in
          (* Nor can it recover a class instance, which no argument's type
             states -- it is named for that reason -- or a type variable no
             parameter spells, such as one only the result names.  Arguments
             are positional, so only the trailing run deduction can recover is
             given up: the instances that lead the list, and every argument up
             to the last one deduction cannot supply, stay. *)
          let is_instance_arg (t : Cpp_ir.Lowered.Type.t) =
            match t with
            | Variable (Index (_, Some id) | Named id) -> Base.Common.is_tc_instance_id id
            | Entity_application (g, _, _) -> ref_is_instance g
            | _ -> false
          in
          let rec instance_prefix = function
            | t :: rest when is_instance_arg t -> t :: instance_prefix rest
            | _ -> []
          in
          (* The arguments were written against the callee's plan, so the
             plan's head says which variable each one is at. *)
          let kept_by_deduction r tys =
            let insts = instance_prefix tys in
            let regular = List.filteri (fun i _ -> i >= List.length insts) tys in
            let undeducible =
              match deducible_tvars_of_glob r with
              | Some deducible ->
                let params =
                  List.filteri
                    (fun i _ -> i >= List.length insts)
                    (Core_plan.Callable_abi.template_head (Calls.callee_abi cx ~instances:(List.length insts) r))
                in
                if List.length params <> List.length regular then None
                else
                  Some
                    (List.map
                       (fun p ->
                         match p.Core_plan.Callable_abi.origin with
                         | Core_plan.Callable_abi.From_scheme v ->
                           not (IntSet.mem (Core.Scheme.Var.ordinal v) deducible)
                         | _ -> true )
                       params )
              | None -> None
            in
            match undeducible with
            | None -> insts
            | Some flags ->
              let rec last_needed i acc = function
                | [] -> acc
                | f :: rest -> last_needed (i + 1) (if f then i + 1 else acc) rest
              in
              let n = last_needed 0 0 flags in
              insts @ List.filteri (fun i _ -> i < n) regular
          in
          (* The arguments are rewritten last first, as {!Cpp_ir.Map} does. *)
          let rec fix_expr (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t = match e with
            | Call (res, Entity (r, (_ :: _ as tys), ci), args)
              when (not (recovered_carrier tys)) && should_strip (List.rev args) ->
              Call
                (res, Entity (r, kept_by_deduction r tys, ci), List.rev (List.map fix_expr (List.rev args)))
            | _ -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:fix_expr ~stmt:fix_stmt ~type_:Fun.id ()) e
          and fix_stmt s = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:fix_expr ~stmt:fix_stmt ~type_:Fun.id ()) s in
          List.map fix_stmt br_stmts
        else br_stmts
      in
      (* Wrap erased pattern variables with any_cast when returned as a template parameter. *)
      let br_stmts =
        match br_ret with
        | Variable _ ->
          let erased_pat_vars =
            List.fold_left (fun acc (p : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Custom_match.param) ->
              if Cpp_ir.Types.prints_as_any p.type_ then Id.Set.add p.name acc else acc)
              Id.Set.empty br_ids
          in
          if Id.Set.is_empty erased_pat_vars then br_stmts
          else
            List.map (fun (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t ->
              match s with
              | Return (Some (Local name))
                when Id.Set.mem name erased_pat_vars ->
                Return (Some (Cpp_passes.Erasure.unbox br_ret (Cpp_ir.Expr.Local name)))
              | s -> s)
              br_stmts
        | _ -> br_stmts
      in
      (br_ids, br_ret, br_stmts) :: gen_cases (i + 1) cs
    | Core.Pattern.Wildcard | Core.Pattern.Bound_variable _ | Core.Pattern.Tuple _ -> gen_cases (i + 1) cs
  in
  let cases = gen_cases 0 (Array.to_list pv) in
  cache_prefix @
  [ Custom_match
      { return_type = case_typ;
        scrutinee = scrut;
        type_args = temps;
        branches =
          List.map
            (fun (params, type_, body) : Cpp_ir.Lowered.phase Cpp_ir.Grammar.Custom_match.branch ->
              {params = params; type_ = type_; body = body})
            cases;
        template = cmatch;
        inductive = Base.Table.indref_of_match pv;
        hold = (if pair_by_value then Owned else Borrowed);
        pieces = Uninstantiated } ]

(* IIFE inlining ({!Cpp_build.inline_iife}), which the statement
    forms here and in {!Effects} rely on.

    When [gen_expr] wraps multi-statement code in an immediately-invoked
    function expression (IIFE):
    {[
      [&]() \{
        unsigned int x = p->px;
        unsigned int y = p->py;
        return (x + y);
      \}()
    ]}
    and the result is consumed at statement level (e.g. by [Return] or
    [Assign]), the lambda wrapper is unnecessary.  [inline_iife] detects
    this pattern and flattens the body statements, replacing the final
    [return] with the enclosing continuation:
    {[
      unsigned int x = p->px;
      unsigned int y = p->py;
      return (x + y);
    ]}
    This produces more readable C++ and avoids interfering with compiler
    optimisations (e.g. copy elision / RVO through a lambda boundary). *)

(** The record [t] a match takes apart into its fields, read once however many
   fields are bound out of it: a call standing in its place is evaluated into
   a temporary first, rather than once per field -- which a recursive call
   taken apart into three fields made three calls per level.  The temporary
   is read for nothing else, so each field is moved out of it.  Returns what
   the fields are read out of, and the statements evaluating it. *)
let record_read_once cx env ~is_typeclass t : Cpp_ir.Lowered.Expr.t * Cpp_ir.Lowered.Stmt.t list =
  let scrut = gen_expr cx env t in
  if is_typeclass || Match_types.is_trivial_scrut scrut then (scrut, [])
  else
    let n = cx.ctx.threaded.cs_counter in
    set_threaded cx (fun t -> { t with cs_counter = n + 1 });
    let cache_id = Base.Common.scrutinee_cache_id n in
    ( Move (Local cache_id),
      match Cpp_build.lift_iife_assignment cache_id None scrut with
      | Some stmts -> stmts
      | None -> [Bind_variable (cache_id, Declare (Auto, None), scrut)] )

(** The custom match of [t] at [typ] with branches [pv] at [case_occ], in
    expression position: an immediately invoked lambda over its template's
    statements. *)
let gen_custom_match_expr cx ?slot env ~typ ~t ~pv ~case_occ : Cpp_ir.Lowered.Expr.t =
  let iife_ret =
    let branch_rty =
      match Array.to_list pv with
      | {Core.Match.Branch.result_type = rty; _} :: _ -> rty
      | [] -> typ
    in
    (* The branches build their values at the slot's type where the
       annotation erased what it states ({!Constructors.refined_by_slot}),
       and so does the lambda returning them. *)
    let branch_rty = match slot with Some s -> Constructors.refined_by_slot s branch_rty | None -> branch_rty in
    let r = Types.cpp_of_core cx env branch_rty in
    if is_cpp_unit_type r
       || Monadic.core_type_is_void_call branch_rty
    then Cpp_ir.Type.Void
    else
      (* The branches are written under the return type in force: where
         that is the annotation's function type grouped otherwise, the
         lambdas they return take their arguments as it groups them. *)
      match Match_types.joined_at ~ret:(current_cpp_return_type cx ()) r with Some t -> t | None -> r
  in
  let stmts =
    let ret =
      match iife_ret with
      | Void -> Some iife_ret
      | _ -> current_cpp_return_type cx ()
    in
    with_cpp_return_type cx ret (fun () ->
        gen_custom_cpp_case cx ?slot env (Destination.return_ cx) typ t pv case_occ )
  in
  Cpp_ir.Build.iife (Some iife_ret) stmts

(** A match taking the record [t] at [typ] apart (the term [core_e]), in
    expression position: a field read, a field called, or the record
    destructured into locals for the one branch's body. *)
let gen_record_projection cx ~expected_ty ~slot env (core_e : Core.Expr.t) ~typ ~t ~pv ~case_occ :
  Cpp_ir.Lowered.Expr.t =
  let {Core.Match.Branch.binders = ids; result_type = r; pattern = pat; body = body} = pv.(0) in
  let n = List.length ids in
  let is_typeclass, record_body =
    match Core_plan.Elaborate.match_kind ~walk:(elaborations cx) typ pv case_occ with
    | Core_plan.Match_kind.Record {typeclass; body} -> (typeclass, body)
    | Custom | Variant -> CErrors.anomaly (Pp.str "gen_expr: a record projection Core did not classify as one")
  in
  (* Build lists that correctly account for erased fields.
     record_fields_of_type includes None entries for erased fields; ids only
     contains non-erased bindings. So Core.Expr.Bound_variable i refers to the i-th non-erased
     field. We filter out None entries for correct indexing. *)
  let all_fields = record_fields_of_type typ in
  let non_erased_fields = List.filter_map Fun.id all_fields in
  let all_field_types =
    match typ with
    | Core.Type.Global_app {head = r; _} -> Base.Table.record_field_types r
    | _ -> []
  in
  let non_erased_field_types =
    filter_value_types all_field_types
  in
  let record_ref_opt =
    match typ with Core.Type.Global_app {head = r; _} -> Some r | _ -> None
  in
  let wrap_record_field_to_api idx access =
    match (record_ref_opt, List.nth_opt non_erased_field_types idx) with
    | Some record_ref, Some core_ty ->
      let tvars = get_current_type_vars cx in
      let storage_ty =
        Types.cpp_ir_of_core_type cx env ~ns:(Core.Ref.User.Set.singleton record_ref) tvars core_ty
      in
      let api_ty = Types.cpp_of_core cx env core_ty in
      Convert.wrap_api_expr ~storage_ty ~api_ty access
    | _ -> access
  in
  (* For type classes, use qualified access (::) instead of arrow (->) since
     type class instances are template type parameters, not runtime values *)
  let make_field_access base_expr fld : Cpp_ir.Lowered.Expr.t =
    if is_typeclass then
      let fld_name = Base.Common.id_of_global Term fld in
      Scope (base_expr, fld_name, [])
    else
      Project
        (base_expr, fld, Match_types.record_field_cpp_ty cx env typ fld)
  in
  (* Strip coercion wrappers from the body — promoted dependent records may
     wrap field references in Core.Expr.Coerce due to Core.Type.Variable/Core.Type.Global_app mismatches *)
  let body' =
    match body with
    | Core.Expr.Coerce {value = b; _}
    | Core.Expr.Boxed_value {value = b; _}
    | Core.Expr.Lambda_group_barrier {value = b; _} -> b
    | b -> b
  in
  ( match (record_body, body') with
  | Projection {field; application = Read}, _ ->
    let fld =
      try Some (List.nth non_erased_fields field) with _ -> None
    in
    ( match fld with
    | Some fld ->
      let access = make_field_access (gen_expr cx env t) fld in
      let access = wrap_record_field_to_api field access in
      if is_typeclass then
        (* For typeclasses, non-function value fields (like m_id : carrier)
           are generated as nullary static methods, so we need () to call
           them *)
        let fld_ty =
          try List.nth non_erased_field_types field
          with _ -> Core.Type.Unknown
        in
        let is_value_field =
          match fld_ty with
          | Core.Type.Arrow _ -> false
          (* A field whose type is itself a typeclass (a superclass field)
             is promoted to a type alias in the instance struct
             ([using ord_eq = eqnat;]), not to a nullary static method, so
             calling it would emit [I::ord_eq()].  It is only ever used as
             a nested-name-specifier for the superclass's projections. *)
          | _ when Base.Table.is_typeclass_type fld_ty -> false
          | _ -> true
        in
        if is_value_field then
          Cpp_ir.Build.call access []
        else
          (* A method named rather than called: curried to the slot as
             a global function would be. *)
          let fld_ty =
            (* At the instance's class type where that is closed: the
               match's own annotation may have erased the arguments. *)
            let class_ty =
              match instance_class_ty ~lex:(current_lexenv cx ()) t with
              | ct when Base.Core_util.type_maxvar ct = 0
                        && not (core_type_contains_erased ct) -> ct
              | _ -> typ
            in
            match class_ty with
            | Core.Type.Global_app {type_arguments = args; _} -> Base.Core_util.type_subst_list args fld_ty
            | _ -> fld_ty
          in
          Coerce.curry_value_to_expected cx env ?expected_ty (Some fld_ty) access
      else
        access
    | _ ->
      CErrors.anomaly (Pp.str "record field index out of bounds") )
  | Projection {field; application = Call | Coerced_call}, Core.Expr.Apply {arguments = args; _} ->
    let fld =
      try Some (List.nth non_erased_fields field) with _ -> None
    in
    let branch_binders =
      List.rev_map (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty)) ids
    in
    let _, env' = push_vars' branch_binders env in
    ( match fld with
    (* Erased arguments ([Core.Expr.Erased_value]) whose parameter is erased
       too are dropped from [value_args]: they are erased type
       parameters (e.g. [A : Type] in [f : forall A, A -> A]) with no C++
       runtime representation.  When the field's codomain erases to [std::any]
       (see [core_codomain_erases_to_any]), wrap the result with
       [std::any_cast<T>] to recover the caller's concrete return type. *)
    | Some fld ->
      (* A record's field is a data member of its type, so a call takes as
         many arguments as that type's function does, through an alias of
         a function type naming it -- [pred nat] is [crane::fn<bool(Nat)>].
         A class's method is a function declared at the field's own arity. *)
      let declared =
        try
          let ty = List.nth non_erased_field_types field in
          Some (if is_typeclass then ty else expand_core_fun_alias ty)
        with _ -> None
      in
      (* An instance keeps a method's own quantifier -- a higher-kinded
         class's every method, and any method parametric in a type of its
         own ([mapf : forall A, (A -> A) -> A -> A]): the method is a member
         template, not a signature erased at [std::any], so neither its
         arguments nor its result are erased here.  The count is the one the
         instance and the concept read ({!Base.Type_util.method_tvar_count}). *)
      let member_template =
        match typ with
        | Core.Type.Global_app {head = r; _} -> Base.Type_util.method_is_member_template r fld
        | _ -> false
      in
      let fld_ty_opt =
        if not member_template then declared
        else
          (* The class's [constructor_argument_types] entry has already erased the method's own
             [forall A]; the projection constant has not. *)
          try Some (strip_erased_method_prefix (callee_core_type_exn cx fld))
          with Not_found -> declared
      in
      (* The field's own parameter types drive erasure of function-valued
         arguments: a class method polymorphic in its own type argument
         takes the canonical [std::function<std::any(std::any...)>], which
         a concrete closure does not convert to. *)
      let fld_param_tys =
        (* Type variables bound by the FIELD itself -- a rank-2 method like
           [forall A, (A -> A) -> A -> A], whose index runs past the class's
           own parameters -- are erased in the generated concept, so every
           instance takes them as [std::any]. *)
        let class_args =
          (* The projection is inlined generically -- the [Core.Expr.Match]'s own
             annotation still says [C A] -- so the instance's arguments come
             off the receiver, which names a concrete instance. *)
          let from_receiver =
            match t with
            | Core.Expr.Global {callee = r; _}
            | Core.Expr.Coerce {value = Core.Expr.Global {callee = r; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Global {callee = r; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Global {callee = r; _}; _} -> (
              match resolve_meta (Base.Table.find_type r) with
              | Core.Type.Global_app {type_arguments = (_ :: _ as args); _} -> Some args
              | _ | (exception Not_found) -> None )
            | _ -> None
          in
          match from_receiver with
          | Some args -> args
          | None -> (
            match typ with Core.Type.Global_app {type_arguments = args; _} -> args | _ -> [] )
        in
        let n_class_params = List.length class_args in
        (* A class parameter the instance fixed at a type extraction erased
           entirely is [std::any] on the instance side (see
           {!Base.Type_util.instance_type_args}); the call has to agree, or it
           passes the wrong number of arguments. *)
        let erased_class_param j =
          match List.nth_opt class_args (j - 1) with
          | Some t -> is_erased_type t
          | None -> false
        in
        (* The field's type as the {e instance} states it: the method's own
           type variables erased, and the class's own replaced by what this
           instance fixed them at.

           Both halves answer the same question -- what does the declaration
           this call resolves to say the parameter's type is.  A class
           parameter left standing renders as [std::any], which is what the
           concept says and not what the instance says, and the two only
           have to agree where the call is saturated.  Where it is not, an
           eta-expanded call synthesises a parameter from this list and
           passes it to a call resolved against the instance, so a parameter
           typed from the class reaches a function declared by the
           instance. *)
        let rec at_instance_args ty =
          match resolve_meta ty with
          | _ when member_template -> ty
          | Core.Type.Variable {variable = j; _} when j > n_class_params || erased_class_param j
            ->
            Core.Type.Unknown
          | Core.Type.Variable {variable = j; _} as ty -> (
            match List.nth_opt class_args (j - 1) with
            | Some arg -> arg
            | None -> ty )
          | Core.Type.Arrow {parameter = a; result = b} ->
            Core.Type.Arrow {parameter = at_instance_args a; result = at_instance_args b}
          | Core.Type.Global_app {head = g; type_arguments = l; index_arguments = a} ->
            Core.Type.Global_app {head = g; type_arguments = List.map at_instance_args l; index_arguments = a}
          | t -> t
        in
        match fld_ty_opt with
        | Some ft ->
          List.filter_map
            (fun t ->
              if erased_by_extraction t || Base.Table.is_typeclass_type t then None
              else Some (at_instance_args t) )
            (fst (get_args_and_ret [] ft))
        | None -> []
      in
      (* An erased argument still fills the slot of a parameter the field
         declares at a live type: extraction dropped the {e value} -- [tok],
         which carries no information -- not the position, and the method
         was generated with the parameter still there.  Such an argument is
         passed as the empty box its parameter's type asks for.  An argument
         whose parameter is erased too simply goes away. *)
      let value_args =
        let is_erased = function Core.Expr.Erased_value _ -> true | _ -> false in
        let dropped = List.filter (fun a -> not (is_erased a)) args in
        let doms =
          match fld_ty_opt with
          | Some ft -> fst (get_args_and_ret [] ft)
          | None -> []
        in
        (* Only a domain list of the field's own arity says anything about
           which argument stands where.  A method whose quantifier was
           stripped back off has fewer domains than the call has arguments,
           and pairing them would shift every position.  A higher-kinded
           class passes its erased type arguments as template arguments
           rather than values, so it keeps dropping them outright. *)
        if member_template || List.length doms <> List.length args then dropped
        else
          List.filteri
            (fun i a -> not (is_erased a) || not (erased_by_extraction (List.nth doms i)))
            args
      in
      (* A class-typed argument is not a value: the concept is met by a type,
         and the method declares it as a template parameter.  It leaves the
         argument list for the callee's explicit template arguments, which is
         the only place that parameter can be given. *)
      (* The arguments live under the branch's binders, so the Core type
         environment is pushed alongside [env'] wherever they are read:
         without it, a binder's type is some other binder's. *)
      let under_branch_binders f =
        let saved_env_types = cx.ctx.lexical.env_types in
        let saved_erased = Binders.save_erased_env cx () in
        Binders.push_binders cx env branch_binders;
        Fun.protect
          ~finally:(fun () ->
            restore_env_types cx saved_env_types;
            Binders.restore_erased_env cx saved_erased )
          f
      in
      let tc_args, _, value_args =
        under_branch_binders (fun () -> Calls.split_instance_args ~lex:(current_lexenv cx ()) value_args)
      in
      let call =
        (* Source order, as {!Coerce.mk_arity_call} takes them. *)
        let arg_exprs =
          under_branch_binders @@ fun () ->
          List.mapi
            (fun j a ->
              let e = gen_stored_value cx ~slot env' a in
              match List.nth_opt fld_param_tys j with
              | Some (Core.Type.Variable_app _ as pt) when not is_typeclass ->
                (* The dictionary's method is stored monomorphically, over
                   the carrier at the erased element, and a carrier does not
                   convert elementwise on its own -- [optional<any>] built
                   from an [optional<Nat>] holds the {e optional}, not the
                   [Nat].  Box the elements on the way in, as the result is
                   unboxed on the way out. *)
                Cpp_ir.Expr.Container_cast (Types.cpp_of_core cx env' pt, e, false)
              | Some pt -> Coerce.erase_fn_arg_for_param cx env' pt a e
              | None -> e )
            value_args
        in
        let callee =
          if not member_template then make_field_access (gen_expr cx env t) fld
          else
            (* The instance's method is a member template (its own [forall A]
               survives), and its type parameters are not always deducible --
               [mret : A -> M A] mentions [A] only in its result -- so they
               are passed explicitly. *)
            let ipv =
              match typ with
              | Core.Type.Global_app {head = r; _} ->
                List.length (Base.Table.get_ind_ip_vars r)
              | _ -> 0
            in
            let nmax =
              match fld_ty_opt with
              | Some ft -> Base.Core_util.type_maxvar ft
              | None -> 0
            in
            if nmax <= ipv then make_field_access (gen_expr cx env t) fld
            else
              let tvars = get_current_type_vars cx in
              let targs =
                List.init (nmax - ipv) (fun k ->
                    Types.cpp_ir_of_core_type cx env tvars
                      (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = (ipv + 1 + k)}) )
              in
              Scope ( gen_expr cx env t,
                  Base.Common.id_of_global Term fld,
                  targs )
        in
        (* The class-typed arguments follow the method's own type variables,
           which is the order the instance declares them in. *)
        let callee =
          match (tc_args, callee) with
          | [], _ -> callee
          | _, Scope (b, id, tys) ->
            Scope
              (b, id, tys @ List.filter_map (fun a -> Calls.core_arg_to_template_type cx env' a) tc_args)
          | _ -> callee
        in
        (* A class method is a static member function of the instance
           struct, so its arity is the field's. *)
        (Coerce.mk_arity_call
             ?params:(Option.map (fun _ -> List.map (Types.cpp_of_core cx env') fld_param_tys) fld_ty_opt)
             ~saturated:(Cpp_ir.Build.call callee)
             arg_exprs)
      in
      let n_value_args = List.length value_args in
      let erased_cod =
        match fld_ty_opt with
        | Some ft -> (not member_template) && core_codomain_erases_to_any n_value_args ft
        | None -> false
      in
      let call = Coerce.recover_boxed_result cx ~boxed:erased_cod ~expected:expected_ty call in
      Coerce.recover_carrier_result
        ~fun_ty:(if is_typeclass then None else fld_ty_opt)
        ~n_args:n_value_args ~want:expected_ty call
    | _ -> CErrors.anomaly (Pp.str "record field index out of bounds") )
  | Destructure, _ | Projection _, _ ->
    (* Destructure record fields into local variables, then evaluate the body
       in an IIFE. push_vars' may rename variables to avoid shadowing
       identifiers already in scope — e.g. when a record has a field
       [rn_value] and the enclosing struct also has an accessor method
       [rn_value], push_vars' renames the local to [rn_value0].

       We must use the renamed ids from push_vars' for the assignment
       declarations so that they are consistent with env' (which the body is
       generated under). Otherwise the declarations would use the original
       names while the body references the renamed ones. *)
    let renamed_ids, env' =
      push_vars'
        (List.rev_map
           (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty))
           ids )
        env
    in
    (* renamed_ids is in reversed order (from List.rev_map above). Reverse it
       back so it aligns with ids (constructor / field order). *)
    let renamed_ids_fwd = List.rev renamed_ids in
    let base, cache = record_read_once cx env ~is_typeclass t in
    let taken = record_taken cx ~is_typeclass t base in
    let asgns =
      List.map
        (fun (i, ((renamed_name, _), (_, ty))) ->
          let fld =
            try Some (List.nth non_erased_fields i) with _ -> None
          in
          let e =
            match fld with
            | Some fld -> make_field_access base fld
            | _ -> CErrors.anomaly (Pp.str "record field index out of bounds")
          in
          let e =
            match typ with
            | Core.Type.Global_app {head = record_ref; _} ->
              let storage_ty =
                Types.cpp_ir_of_core_type cx env ~ns:(Core.Ref.User.Set.singleton record_ref) [] ty
              in
              let api_ty = Types.cpp_ir_of_core_type cx env [] ty in
              Convert.wrap_api_expr ~storage_ty ~api_ty e
            | _ -> e
          in
          let decl_ty =
            Types.cpp_ir_of_core_type cx env [] ty
          in
          let binder = local_binder cx ~site:(Branch (case_occ, 0)) env' renamed_name in
          let stmts =
            match
              Cpp_build.lift_iife_assignment renamed_name (Some decl_ty) e
            with
            | Some stmts -> stmts
            | None -> [Cpp_ir.Stmt.Bind_variable (renamed_name, Declare (decl_ty, binder), e)]
          in
          (stmts, taken || (is_typeclass && match decl_ty with Reference _ -> false | _ -> true)) )
        (List.mapi (fun i x -> (i, x)) (List.combine renamed_ids_fwd ids))
    in
    Match_types.value_iife ?ret:expected_ty cx env (Some r)
      (cache @ List.concat_map fst asgns
       @ Binders.with_binders cx env renamed_ids (fun () ->
             if Base.Probe.checking () then
               List.iteri
                 (fun i _ ->
                   Representation_plan.check ~as_bound:true cx.ctx ~site:(Branch (case_occ, 0)) ~field:i
                     ~live:(Binders.binder_is_boxed cx (n - i)) () )
                 ids;
             with_iife_return_type cx expected_ty (fun () ->
                 with_fields_plan cx core_e asgns (fun () ->
                     gen_stmts cx ~slot env' (Destination.return_ cx) body ) ) ) ) )
  (* Known limitation: simultaneous pattern matching on record fields is not
     supported — each field is destructured individually. *)

(** A match taking the record [t] at [typ] apart (the term [ast]), in
    statement position ending in [k]: the scrutinee read once, its fields
    declared as locals, then the one branch's statements. *)
let gen_record_match_stmts cx ~slot env (k : Destination.t) (ast : Core.Expr.t) ~typ ~t
  ~pv ~case_occ : Cpp_ir.Lowered.Stmt.t list =
  let {Core.Match.Branch.binders = ids; body = body; _} = pv.(0) in
  let n = List.length ids in
  let is_typeclass, is_simple =
    match Core_plan.Elaborate.match_kind ~walk:(elaborations cx) typ pv case_occ with
    | Core_plan.Match_kind.Record {typeclass; body = Projection {application = Read | Call; _}} -> (typeclass, true)
    | Record {typeclass; body = Projection {application = Coerced_call; _} | Destructure} -> (typeclass, false)
    | Custom | Variant -> CErrors.anomaly (Pp.str "gen_stmts: a record projection Core did not classify as one")
  in
  if is_simple then
    (* Simple body: gen_expr handles these as direct field access (no IIFE),
       so delegate to the default path. *)
    let value =
      gen_expr_typed cx ?expected_ty:(Coerce.position_cpp_ty cx None) env ast
    in
    (* A function value returned into an erased ([std::any]) return type --
       e.g. the [nat -> nat] branch of a dependent [if ... then nat else
       nat -> nat] -- must be stored in the canonical adapter form the
       application site casts back to. *)
    let value =
      match Option.map (Types.slot_repr_of_cpp_type cx) (current_cpp_return_type cx ()) with
      | Some (Boxed kind) ->
        Typed_checks.adapted ~before:value (current_cpp_return_type cx ())
          (Coerce.box_for_any_slot cx kind ast value.expr)
      | Some Native | None -> value
    in
    Destination.finish_inlined cx k value
  else
    (* Complex body: emit field extraction assignments as flat statements
       instead of wrapping in an IIFE. This produces clean code for all
       continuations (return, assignment, etc.). *)
    let all_fields = record_fields_of_type typ in
    let non_erased_fields = List.filter_map Fun.id all_fields in
    let make_field_access base_expr fld : Cpp_ir.Lowered.Expr.t =
      if is_typeclass then
        let fld_name = Base.Common.id_of_global Term fld in
        Scope (base_expr, fld_name, [])
      else
        Project (base_expr, fld, Match_types.record_field_cpp_ty cx env typ fld)
    in
    let renamed_ids, env' =
      push_vars'
        (List.rev_map
           (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty))
           ids )
        env
    in
    let renamed_ids_fwd = List.rev renamed_ids in
    let tvars = get_current_type_vars cx in
    let base, cache = record_read_once cx env ~is_typeclass t in
    let taken = record_taken cx ~is_typeclass t base in
    let asgns =
      List.map
        (fun (i, ((renamed_name, _), (_, ty))) ->
          let fld =
            try Some (List.nth non_erased_fields i) with _ -> None
          in
          let e =
            match fld with
            | Some fld -> make_field_access base fld
            | _ ->
              CErrors.anomaly (Pp.str "record field index out of bounds")
          in
          let e =
            match typ with
            | Core.Type.Global_app {head = record_ref; _} ->
              let storage_ty =
                Types.cpp_ir_of_core_type cx env ~ns:(Core.Ref.User.Set.singleton record_ref) tvars ty
              in
              let api_ty = Types.cpp_of_core cx env ty in
              Convert.wrap_api_expr ~storage_ty ~api_ty e
            | _ -> e
          in
          let api_ty_for_decl =
            Types.cpp_of_core cx env ty
          in
          let decl_ty : Cpp_ir.Lowered.Type.t =
            if Base.Type_util.has_tany_in_type api_ty_for_decl then
              Reference (Lvalue, Const Auto)
            else
              api_ty_for_decl
          in
          let binder = local_binder cx ~site:(Branch (case_occ, 0)) env' renamed_name in
          let stmts : Cpp_ir.Lowered.Stmt.t list =
            match
              Cpp_build.lift_iife_assignment renamed_name (Some decl_ty) e
            with
            | Some stmts -> stmts
            | None -> [Bind_variable (renamed_name, Declare (decl_ty, binder), e)]
          in
          (* A class instance's field is a static member: the local copies
             it, and is its own. *)
          (stmts, (taken || is_typeclass) && match decl_ty with Reference _ -> false | _ -> true) )
        (List.mapi (fun i x -> (i, x)) (List.combine renamed_ids_fwd ids))
    in
    Binders.push_binders cx env (Match_types.retype_dependent_params typ renamed_ids);
    if Base.Probe.checking () then
      List.iteri
        (fun i _ ->
          Representation_plan.check cx.ctx ~site:(Branch (case_occ, 0)) ~field:i
            ~live:(Binders.binder_is_boxed cx (n - i)) () )
        ids;
    let body_stmts =
      with_fields_plan cx ast asgns (fun () -> gen_stmts cx ~slot env' k body)
    in
    cache @ List.concat_map fst asgns @ body_stmts
