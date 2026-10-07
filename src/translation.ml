(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** MiniML to MiniCpp translation: converts ML-style AST to C++-oriented AST.

    The recursive core here -- {!gen_expr}, {!gen_stmts}, {!eta_fun}, the
    call, match and fixpoint generators -- builds on three layers it
    includes: {!Translation_support} (field naming, monads, type variables,
    ownership), {!Translation_types} (type conversion, erasure, binder types,
    coercions) and {!Translation_calls} (call planning).  None of them
    recurses through expression generation; type conversion reaches it only
    through {!Translation_types.type_term_arg}. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Util
(* Re-export the shared translation state so it is available unqualified here
   and still reachable as [Translation.<accessor>] by external callers (via
   translation.mli). *)
include Translation_state
include Ml_type_util
include Translation_support
include Translation_types
include Translation_calls

(* How a match branch reads a field of the constructor it matched: as the
   structured binding has it; through the pointer the field is stored behind
   (a recursive field, or under [Crane BoxedFields] one holding an inductive);
   or through [crane::unbox] (a type-parameter field under [Crane
   BoxedFields], boxed or not per instantiation). *)
type field_read = Read_as_bound | Read_through_pointer | Read_unboxed

(** Generate local fixpoint declarations using the Y-combinator pattern
    for escaping fixpoints.

    Replaces the [shared_ptr<std::function>] pattern with a generic-lambda
    self-passing pattern:
    {v
      auto go_impl = [=](auto &_self, A... args) mutable -> R {
        ... _self(_self, args) ...
      };
      auto go = [=](A... args) mutable -> R {
        return go_impl(go_impl, args...);
      };
    v}

    No heap allocation, no [std::function] type erasure.  The [auto &_self]
    parameter uses C++14 generic lambdas.

    For mutual recursion with N functions, each impl takes N self parameters:
    {v
      auto f_impl = [=](auto &_sf, auto &_sg, A...) { ... _sg(_sf, _sg, ...) ... };
      auto g_impl = [=](auto &_sf, auto &_sg, A...) { ... _sf(_sf, _sg, ...) ... };
      auto f = [=](A...) { return f_impl(f_impl, g_impl, ...); };
      auto g = [=](A...) { return g_impl(f_impl, g_impl, ...); };
    v}

    @return [(decls, defs, deref_subst)] where [defs] is empty and
    [deref_subst] is the identity function (no dereferencing needed).
    @see gen_local_fix_by_ref for the non-escaping alternative. *)
let gen_local_fix_ycomb env renamed_ids funs_with_params =
  let ret_ty ty =
    match cpp_of_ml env ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (Tv_index (_, None)) -> None
      | _ -> Some t )
    | _ -> None
  in
  (* Create self-parameter IDs and impl IDs for each fixpoint. *)
  let self_ids =
    List.map
      (fun (id, _) -> Id.of_string ("_self_" ^ Id.to_string id))
      renamed_ids
  in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  let rewrite_expr, rewrite_stmt = self_call_rewriter renamed_ids self_ids in
  (* Generate impl lambdas: each takes all self params (auto &) + original params. *)
  let impl_stmts =
    List.map2
      (fun ((_fix_id, fty), impl_id) (args, body) ->
        let self_params =
          List.rev_map (fun sid -> (Tref (Lvalue, Tauto), Some sid)) self_ids
        in
        let orig_params =
          List.map
            (fun (id, ty) ->
              (cpp_of_ml env ty, Some id))
            args
        in
        Sasgn
          ( impl_id,
            Declare Tauto,
            CPPlambda
              { cl_tparams = [];
                cl_moved = [];
                cl_params = of_reversed (orig_params @ self_params);
                cl_ret = ret_ty fty;
                cl_body = List.map rewrite_stmt body;
                cl_capture = Closure } ))
      (List.combine renamed_ids impl_ids)
      funs_with_params
  in
  (* Generate wrapper lambdas: forward to impl with all impl_ids prepended. *)
  let impl_vars_rev = List.rev_map (fun id -> CPPvar id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun ((fix_id, fty), impl_id) (args, _body) ->
        let orig_params =
          List.map
            (fun (id, ty) ->
              (cpp_of_ml env ty, Some id))
            args
        in
        let fwd_args =
          List.map (fun (id, _) -> CPPvar id) args @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call = CPPfun_call (call_opaque, CPPvar impl_id, of_reversed fwd_args) in
        let wrapper_body =
          match rty with
          | None -> [Sexpr call]
          | _ -> [Sreturn (Some call)]
        in
        Sasgn
          ( fix_id,
            Declare Tauto,
            CPPlambda
              { cl_params = of_reversed orig_params;
              cl_tparams = [];
              cl_moved = [];
                cl_ret = rty;
                cl_body = wrapper_body;
                cl_capture = Closure } ))
      (List.combine renamed_ids impl_ids)
      funs_with_params
  in
  let deref_subst stmts = stmts in
  (impl_stmts @ wrapper_stmts, [], deref_subst)

(** Generate local fixpoint declarations using the [\[&\]]-capture pattern.

    Used when {!fixpoint_escapes_in_stmts} returns [false], meaning the
    fixpoint variable is only used in direct call position and never
    escapes into a closure or data structure.  The [\[&\]] capture is
    lightweight (no heap allocation, no indirection) but creates dangling
    references if the closure outlives the enclosing scope.

    Uses a Y-combinator pattern to avoid [std::function] type erasure
    overhead (heap allocation, virtual dispatch).  Parameters are passed
    by value (same as the old pattern) to preserve move/mutation semantics.

    Generated C++:
    {v
      auto f_impl = [&](auto& _self_f, A a, B b) -> R {
        ... _self_f(_self_f, a', b') ...
      };
      auto f = [&](A a, B b) -> R {
        return f_impl(f_impl, a, b);
      };
    v}

    @return [(decls, defs)] — declaration and definition statement lists.
    @see gen_local_fix_shared_ptr for the escaping-fixpoint alternative. *)
let gen_local_fix_by_ref env renamed_ids funs_with_params owned_flags_per_fun =
  let ret_ty ty =
    match cpp_of_ml env ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (Tv_index (_, None)) -> None
      | _ -> Some t )
    | _ -> None
  in
  let self_ids =
    List.map
      (fun (id, _) -> Id.of_string ("_self_" ^ Id.to_string id))
      renamed_ids
  in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  let rewrite_expr, rewrite_stmt = self_call_rewriter renamed_ids self_ids in
  let impl_stmts =
    List.map2
      (fun (((_fix_id, fty), impl_id), owned_flags) (args, body) ->
        let self_params =
          List.rev_map (fun sid -> (Tref (Lvalue, Tauto), Some sid)) self_ids
        in
        let orig_params =
          List.map2
            (fun (id, ty) owned ->
              let cpp_ty =
                cpp_of_ml env ty
              in
              ( wrap_param_by_ownership ~is_owned:owned cpp_ty,
                Some id ))
            args owned_flags
        in
        Sasgn
          ( impl_id,
            Declare Tauto,
            CPPlambda
              { cl_params = of_reversed (orig_params @ self_params);
              cl_tparams = [];
              cl_moved = [];
                cl_ret = ret_ty fty;
                cl_body = List.map rewrite_stmt body;
                cl_capture = Immediate } ))
      (List.combine (List.combine renamed_ids impl_ids) owned_flags_per_fun)
      funs_with_params
  in
  let impl_vars_rev = List.rev_map (fun id -> CPPvar id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun (((fix_id, fty), _impl_id), owned_flags) (args, _body) ->
        let orig_params =
          List.map2
            (fun (id, ty) owned ->
              let cpp_ty =
                cpp_of_ml env ty
              in
              ( wrap_param_by_ownership ~is_owned:owned cpp_ty,
                Some id ))
            args owned_flags
        in
        let fwd_args =
          List.map (fun (id, _) -> CPPvar id) args @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call = CPPfun_call (call_opaque, CPPvar _impl_id, of_reversed fwd_args) in
        let wrapper_body =
          match rty with
          | None -> [Sexpr call]
          | _ -> [Sreturn (Some call)]
        in
        Sasgn
          ( fix_id,
            Declare Tauto,
            CPPlambda
              { cl_params = of_reversed orig_params;
              cl_tparams = [];
              cl_moved = [];
                cl_ret = rty;
                cl_body = wrapper_body;
                cl_capture = Immediate } ))
      (List.combine (List.combine renamed_ids impl_ids) owned_flags_per_fun)
      funs_with_params
  in
  (impl_stmts @ wrapper_stmts, [])


let rec gen_expr_custom_cons ?expected_ty ?(slot = empty_slot) env (ty : ml_type)
    r ts =
  (* Extraction leaves a type argument [Tunresolved] where it could not read the
     type off the term -- the element of [Some 1] passed at a parameter of an
     inductive that applies its own higher-kinded parameter ([F nat]).  The
     constructor's own field types say which type argument each value argument
     pins down, so recover it from the argument.  Left as [Tunresolved] the
     argument erases to [std::any], and the erased instantiation
     ([optional<std::any>]) does not match the field's declared one.

     Not when this value is itself being built into an erased slot: there the
     erased instantiation is the canonical one, and pinning the argument down
     is exactly what makes the consumer's fixed [any_cast] throw. *)
  let ty =
    match ty with
    | Miniml.Tglob (n, tys, sc)
      when List.exists (fun t -> t = Miniml.Tunknown) tys
           && (not slot.deep_erase)
           (* Nor when the destination is (or contains) [std::any]: there the
              erased shape is the canonical one every producer has to agree
              on, and grounding this one is what makes the consumer's fixed
              [any_cast] throw. *)
           && (not
                 ( match expected_ty with
                 | Some t -> has_tany_in_type (unfold_cpp_typedef env t)
                 | None -> false ))
           && not
                ( match (!tctx).current_cpp_return_type with
                | Some t -> resolves_to_any_type t
                | None -> false ) ->
      let field_tys =
        match Table.get_ctor_ip_types_opt r with
        | Some l -> List.filter (fun t -> not (Mlutil.isTdummy t)) l
        | None -> []
      in
      let recovered = Array.of_list tys in
      List.iteri
        (fun i ft ->
          match (ft, List.nth_opt ts i) with
          | (Miniml.Tvar (_, k)), Some arg
            when k >= 1
                 && k <= Array.length recovered
                 && recovered.(k - 1) = Miniml.Tunknown ->
            ( match ml_ast_type_hint arg with
            | Some arg_ty -> recovered.(k - 1) <- arg_ty
            | None -> () )
          | _ -> () )
        field_tys;
      (* A nullary constructor ([None]) carries no argument to read the type
         off, so the only remaining witness is the slot it is being built
         into -- the field type of an enclosing constructor, instantiated. *)
      ( match Option.map resolve_tmeta slot.expected_ml_ty with
      | Some (Miniml.Tglob (exp_n, exp_tys, _))
        when GlobRef.CanOrd.equal n exp_n
             && List.length exp_tys >= Array.length recovered ->
        (* Aligned at the right: a type constructor that reached the slot
           partially applied ([F] at [F A]) keeps the placeholder arguments it
           was carrying in front of the ones applied to it. *)
        (* Only a type this scope can write is worth taking.  That is not the
           same as a ground one: [list (A * B)] in a declaration that binds
           [A] and [B] is as writable as [list nat], and refusing it leaves a
           nullary constructor at [list<pair<any, any>>] inside a function
           whose every neighbour spells [T1] and [T2].  What must be refused
           is a variable from {e another} scope -- a slot read off an
           abstract carrier ([m_carrier M]) -- which would not compile. *)
        let rec is_writable = function
          | Miniml.Tglob (_, args, _) -> List.for_all is_writable args
          | Miniml.Tarr (a, b) -> is_writable a && is_writable b
          | Miniml.Tmeta {contents = Some t} -> is_writable t
          | Miniml.Tvar (_, _) as t ->
            names_only_scoped_tvars (cpp_of_ml env t)
          | Miniml.Tapp _ | Miniml.Tunknown | Miniml.Tmeta {contents = None} ->
            false
          | _ -> true
        in
        let m = Array.length recovered in
        List.iteri
          (fun i t ->
            let i = i - (List.length exp_tys - m) in
            if i >= 0 && recovered.(i) = Miniml.Tunknown && is_writable t then
              recovered.(i) <- t )
          exp_tys
      | _ -> () );
      Miniml.Tglob (n, Array.to_list recovered, sc)
    | _ -> ty
  in
  (* The same reading of the slot, but pointwise and at any depth.  A type
     argument the term never spells -- the element of a [nil] nested inside a
     pair -- arrives erased wherever it sits, while the position states the
     whole shape; the recovery above only looks at the constructor's own
     outermost arguments. *)
  let ty =
    if
      slot.deep_erase
      || ( match expected_ty with
         | Some t -> has_tany_in_type (unfold_cpp_typedef env t)
         | None -> false )
    then ty
    else
      match slot.expected_ml_ty with
      | None -> ty
      | Some want ->
        Ml_type_util.refine_erased
          ~writable:(fun t -> names_only_scoped_tvars (cpp_of_ml env t))
          ty want
  in
  (* A position the term leaves unknown that the expected C++ type states as
     one of this scope's own variables -- [Some (tfmap f t)] returned at
     [std::optional<T1>] -- is that variable.  Only a variable: it is the one
     C++ type with an ML reading to take back. *)
  let ty =
    (* With no slot of its own, a constructor in a tail statement lands in
       the enclosing function's result ({!with_cpp_return_type}, as
       {!position_cpp_ty} reads it). *)
    let expected =
      match expected_ty with
      | Some _ -> expected_ty
      | None -> (!tctx).current_cpp_return_type
    in
    match (ty, Option.map (fun t -> Ml_type_util.unqualify_ty (unfold_cpp_typedef env t)) expected) with
    | Miniml.Tglob (n, tys, sc), Some (Tglob (n', etys, _))
      when GlobRef.CanOrd.equal n n' && List.length tys = List.length etys
           && (not slot.deep_erase) ->
      Miniml.Tglob
        ( n,
          List.map2
            (fun t e ->
              match (resolve_tmeta t, e) with
              | (Miniml.Tunknown | Miniml.Tmeta {contents = None}),
                Tvar (Tv_index (i, _))
                when names_only_scoped_tvars e ->
                Miniml.Tvar (Miniml.Schematic, i)
              | _ -> t )
            tys etys,
          sc )
    | _ -> ty
  in
  (* Try to fold binary positive chains inside Z/N constructors to avoid
     unsigned-int overflow.  Zpos(xI(xO(...xH...))) and Zneg(...) chains
     are folded into INT64_C(n) / INT64_C(-n) literals when the parent
     inductive has a numeral format registered via Crane Extract Numeral. *)
  let folded =
    match (r, ts) with
    | GlobRef.ConstructRef ((kn, i), cidx), [inner] ->
      let ind_ref = GlobRef.IndRef (kn, i) in
      ( match Table.get_numeral_info ind_ref with
      | Some info -> try_fold_z_binary info cidx inner
      | None -> None )
    | _ -> None
  in
  match folded with
  | Some e -> e
  | None ->
  (* Some custom-extracted inductives (e.g. [sum1], registered as
     [Crane Extract Inductive sum1 => "" ["%a0" "%a0"]]) are pure type-level
     erasure markers: their constructor template forwards the argument
     completely unboxed, with no runtime wrapper type at all. For these, the
     generic "erase Tvar-typed fields into std::any" logic below must NOT
     fire, because there is no field storage to box into — the value must
     stay exactly as it was produced. Wrapping it anyway makes the erased
     [std::any] hold the argument's own (possibly unique closure) type
     instead of whatever a downstream consumer expects inside that [std::any]
     (e.g. [itree_vis] expects [std::function<std::any()>], not a bare
     lambda), and the mismatched [std::any_cast] throws at runtime
     (CWE-704, finding 44). *)
  let is_passthrough_ctor_arg i =
    match r with
    | GlobRef.ConstructRef ((kn, mi), cidx) ->
      ( try
          let tmpl = List.nth (Table.find_custom_ctor_templates (kn, mi)) (cidx - 1) in
          String.trim tmpl = Printf.sprintf "%%a%d" i
        with _ -> false )
    | _ -> false
  in
  (* PROMOTED TYPE VARIABLES in constructor expressions: Use module-level
     aliases (std::any) instead of template-qualified types.

     Inside a template function taking a typeclass parameter, promoted type vars
     normally resolve via [promoted_var_map]:
       [m_carrier] ↦ [typename _tcI0::m_carrier]

     But constructor expressions are NOT in template scope — they're module-level
     static initializers:
       static inline const Functor forward_functor = ...;

     Here, there's no [_tcI0] to qualify. Instead, promoted vars use the
     module-level [using] declaration:
       using Obj = std::any;
       using Hom = std::any;

     So [object_of forward_functor 7] becomes:
       forward_functor->object_of(7u)  // returns std::any
       std::any_cast<unsigned int>(...)  // cast to concrete type

     Setting [in_constructor_expr] makes unresolvable promoted vars (those
     NOT in [promoted_var_map]) fall back to [Tany] = [std::any].

     We do NOT clear [promoted_var_map] here: inside template functions,
     promoted vars must resolve to qualified types (e.g., typename _tcI0::Obj)
     so that constructor type args match the function's declared return type.
     At module level, [promoted_var_map] is already empty, so the
     [in_constructor_expr] fallback handles it naturally. *)
  (* Inside a polymorphic function object the erased type the ML annotation
     withheld is the lambda's own template parameter, so a type-argument list
     erasure left empty says the carrier rather than printing [std::any] for a
     value the parameter has already pinned down.  See {!Rank2}. *)
  let type_args_at_carrier r =
    match get_rank2_carrier () with
    | Some x -> Option.default [] (Rank2.type_args_at_carrier x r)
    | None -> []
  in
  let result =
    with_in_constructor_expr true @@ fun () ->
  (* Convert value arguments to C++ expressions.

     Erased proof/type arguments ([MLdummy]) produce [std::any{}] rather
     than [CPPabort]: the corresponding C++ parameter type is [std::any]
     (all erased types map to [std::any]), and custom constructors like
     [std::make_pair] are evaluated eagerly so a throw would crash at
     runtime.  This mirrors the [gen_ctor_arg] in the [MLcons] case of
     {!gen_expr}. *)
  (* Generate constructor arguments with live move_dead_after so the move
     analysis can fire for single-use variables (nb_occur_match = 1 already
     prevents moving variables that appear more than once across all args). *)
  let gen_ctor_arg ?expected_ty ?(slot = slot) e =
    match e with
    | MLdummy _ -> Cpp_erasure.empty_box
    | e when ml_value_is_void_call e ->
      wrap_void_call_as_value (gen_expr ~slot env e)
    | _ -> gen_expr ?expected_ty ~slot env e
  in
  (* Generate args with expected type hints: pass the i-th type arg of the constructor's inductive type before generating
     the i-th value arg.  This allows gen_ctor_call to recover concrete element
     types for nil lists whose ML annotation has unresolved metas (Tmeta{None}).
     Specifically: in pair(fr, nil), the pair type args [A, B] tell us B = list(A),
     so the nil's element type can be recovered as A even if its annotation is Tmeta. *)
  (* Try to get type args from the pair type annotation, falling back to the
     outer [expected_ml_ty] (set by an enclosing MLletin or MLapp
     lookahead) when the pair type itself is erased (Tmeta{None}). This
     recovers the expected element type for nil args in pairs like
       let sk0 : parser_frame × list(parser_frame) = (fr(...), nil)
     where the pair MLcons has type annotation Tmeta{None}. *)
  let ty_args_for_expected =
    let rec deep_resolve ty =
      match resolve_tmeta ty with
      | Miniml.Tglob (n, tys, s) -> Miniml.Tglob (n, List.map deep_resolve tys, s)
      | Miniml.Tarr (t1, t2) -> Miniml.Tarr (deep_resolve t1, deep_resolve t2)
      | t -> t
    in
    (* Also try the expected type from the enclosing let-binding when deep_resolve
       can't resolve sub-metas in the pair's own type annotation.
       The expected type comes from t_effective which may have different (resolved) metas. *)
    let fallback_from_expected tys =
      if List.exists (ml_type_contains_erased ~in_arrows:true) tys then
        match slot.expected_ml_ty with
        | Some exp ->
          let ctor_ind = match r with
            | GlobRef.ConstructRef ((kn, i), _) -> Some (GlobRef.IndRef (kn, i))
            | _ -> None
          in
          (match deep_resolve exp, ctor_ind with
          | Miniml.Tglob (exp_n, exp_tys, _), Some ind
            when GlobRef.CanOrd.equal exp_n ind
                 && List.length exp_tys = List.length tys ->
            (* An arrow the annotation left unresolved is erasure too -- the
               closure inside an [option (nat -> nat)] is precisely what the
               slot knows and the annotation does not.  The slot's answer is
               only usable where no type variable survives in it: one that does
               names a template parameter out of scope here, and would print as
               a bare [T1]. *)
            List.map2 (fun local outer ->
              if ml_type_contains_erased ~in_arrows:true local
                 && not (Ml_type_util.ml_type_contains_tvar outer)
              then outer else local) tys exp_tys
          | _ -> tys)
        | None -> tys
      else tys
    in
    match deep_resolve ty with
    | Miniml.Tglob (_, tys, _) -> fallback_from_expected tys
    | _ ->
      (match slot.expected_ml_ty with
      | Some exp ->
        let ctor_ind = match r with
          | GlobRef.ConstructRef ((kn, i), _) -> Some (GlobRef.IndRef (kn, i))
          | _ -> None
        in
        (match deep_resolve exp, ctor_ind with
        | Miniml.Tglob (exp_n, exp_tys, _), Some ind
          when GlobRef.CanOrd.equal exp_n ind -> exp_tys
        | _ -> [])
      | None -> [])
  in
  (* Pre-compute field types and draft template types so we can wrap lambdas
     that are stored in erased (std::any) fields.  This mirrors the logic in
     wrap_if_needed_for_field for the standard MLcons path. *)
  let field_types_for_wrap = match Table.get_ctor_ip_types_opt r with
    | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
    | None -> [] in
  let draft_ctor_temps_for_wrap = match ty with
    | Miniml.Tglob (cn, raw_tys, _) ->
      let tys = match cn with
        | GlobRef.IndRef (kn, _) ->
          (match Table.get_ind_num_param_vars_opt kn with
          | Some nv -> safe_firstn nv raw_tys
          | None -> raw_tys)
        | _ -> raw_tys
      in
      (* Resolve against the enclosing type-variable names: inside a member
         template a [Tvar] is a real parameter, not an erased type. *)
      let temps = template_params_of_ml env tys in
      (* When all type args are erased and promoted_var_map is active, use
         concrete promoted types so elements don't get wrapped in std::any. *)
      if List.for_all prints_as_any temps && (!tctx).promoted_var_map <> [] then
        match promoted_tys_of_arity (List.length tys) with
        | Some promoted_tys -> promoted_tys
        | None -> temps
      else if List.for_all prints_as_any temps then
        (* The constructor's own annotation was erased, but the enclosing
           method declares the very same type with its arguments intact --
           inside a member template, [Some a] returning [optional<_A0>]. *)
        match (!tctx).current_cpp_return_type with
        | Some (Tglob (rn, rargs, _))
          when GlobRef.CanOrd.equal rn cn
               && List.length rargs = List.length temps
               && not (List.exists prints_as_any rargs) ->
          rargs
        | _ -> temps
      else temps
    | _ -> []
  in
  (* These are storage slots: writing a field down as [std::any] is what makes
     the value in it boxed, so a slot whose representation was merely unknown
     becomes known-boxed here (see {!materialise_opaque}).  Without this a
     payload declared [pair<std::any, std::any>] would store its components
     raw, and the consumer's [any_cast] on them would throw. *)
  let draft_ctor_temps_for_wrap =
    List.map materialise_opaque draft_ctor_temps_for_wrap
  in
  (* The same slots, read off the destination instead of off this
     constructor's own annotation.  A locally concrete value can be built into
     a slot that names a more erased instantiation of the same type -- a
     [pair<List<std::any>, std::any>] field of a [sigT] receiving a
     [(l, @length A)] whose components are concrete here -- and it is the
     destination's shape that every consumer reads back, so a component
     landing in one of its erased positions has to be boxed.

     It goes the other way too, and for the same reason.  This constructor's
     own annotation can name a type variable the enclosing scope has no
     spelling for -- the [A] of the [bind] whose callback this body is -- and
     [std::any] is then not a statement that the position is boxed, only that
     the annotation could not be written here.  The destination can write it:
     the call that takes this value spells the very type [A] stands for
     ([typename _tcI0::iptr]).  Where one side is erased and the other is not,
     the one that says something is the one to believe; where both say
     something, the local instantiation is the more precise. *)
  let ctor_temps_at_slot =
    match (expected_ty, r) with
    | Some exp, GlobRef.ConstructRef ((kn, i), _) -> (
      match unfold_cpp_typedef env exp with
      | Tglob (en, eargs, _)
        when GlobRef.CanOrd.equal en (GlobRef.IndRef (kn, i))
             && List.length eargs = List.length draft_ctor_temps_for_wrap ->
        List.map2
          (fun local slot ->
            if slot = Tany then Tany
            else if prints_as_any local then slot
            (* Erased only in part -- [pair<std::any, ...>] where a field's
               class variable had no instance in scope -- the destination
               fills the part it knows, [St<ptr>]. *)
            else if Ml_type_util.has_tany_written local then
              Ml_type_util.refine_erased_by ~expected:slot local
            else local )
          draft_ctor_temps_for_wrap eargs
      | _ -> draft_ctor_temps_for_wrap )
    | _ -> draft_ctor_temps_for_wrap
  in
  (* Whether the destination spelled position [j] concretely.  A type that
     writes its arguments down -- [std::pair<std::any, Exp<std::any>>] -- has
     thereby said which of them are boxed and which are not, and a statement
     beats the inference below, which concludes from one erased argument that
     every position is read back erased.  That inference is sound only where
     the erasure is invisible in the C++ type. *)
  let slot_states_unboxed j =
    match (expected_ty, r) with
    | Some exp, GlobRef.ConstructRef ((kn, i), _) -> (
      match unfold_cpp_typedef env exp with
      (* A statement is a spelling that boxes some positions and not others;
         one that boxes none is this value's own type, which the deep
         erasure asked for by its destination overrides. *)
      | Tglob (en, eargs, _)
        when GlobRef.CanOrd.equal en (GlobRef.IndRef (kn, i))
             && List.exists prints_as_any eargs -> (
        match List.nth_opt eargs j with
        | Some t -> not (prints_as_any t)
        | None -> false )
      | _ -> false )
    | _ -> false
  in
  (* Whether this constructor's value lands in a DEEPLY erased slot: one
     whose consumer does not merely read a [std::any] back, but
     reconstructs the shape underneath it and reads every component boxed
     as well ([any_cast<pair<any,any>>]).  Two things put a value in that
     position, and they mean the same thing:

     - a sibling field of this very constructor is erased, so the whole
       tuple is read back in erased form -- e.g. [(v, tt)] at
       [symbols_semty [x] = prod (symbol_semty x) unit], where the first
       component is erased and the second is a concrete [unit];
     - the value flows straight out into a value-dependent erased slot,
       the enclosing function's C++ return type having resolved to
       [std::any] (e.g. [domty n], a type-level match).

     In both cases a concrete component stored as itself would produce
     [pair<string, monostate>], which the consumer's
     [any_cast<pair<any,any>>] cannot recover.  A custom LIST cons is
     excluded from the second case: its elements keep their own container
     type (see [is_already_container] below).  *)
  let is_list_cons_ctor =
    match r with
    | GlobRef.ConstructRef ((kn, _), _) ->
      let ind = GlobRef.IndRef (kn, 0) in
      Ml_type_util.is_custom_list_global ind
    | _ -> false
  in
  (* "A sibling field is erased" is a statement about fields, so only the
     type arguments this constructor's fields actually stand at count.
     [itreeF]'s event index erases -- no [E] has a C++ spelling -- and
     [RetF]'s one field is an [R]; reading the erasure off the whole
     argument list would box that field for a reason no field of [RetF]
     has anything to do with. *)
  let erased_arg_under_a_field =
    let occupied =
      List.fold_left collect_tvars [] field_types_for_wrap
    in
    (* Read at the destination's refinement, as [field_slot] below is: a
       field the annotation erased and the destination writes is not
       erased. *)
    List.exists
      (fun j -> List.nth_opt ctor_temps_at_slot (j - 1) = Some Tany)
      occupied
  in
  let slot_is_deeply_erased =
    erased_arg_under_a_field
    || ((not is_list_cons_ctor)
        && match (!tctx).current_cpp_return_type with
           | Some t -> resolves_to_any_type t
           | None -> false)
  in
  let args =
    List.rev (List.mapi (fun i e ->
      let saved_ret = (!tctx).current_cpp_return_type in
      let new_expected =
        match List.nth_opt field_types_for_wrap i with
        | Some (Miniml.Tvar (_, j) as ft) -> (
          match List.nth_opt ty_args_for_expected (j - 1) with
          | Some (Tdummy _) | None -> Some ft
          | x -> x )
        | Some ft when ty_args_for_expected <> [] ->
          Some (Mlutil.type_subst_list ty_args_for_expected ft)
        | Some ft -> Some ft
        | None ->
        match List.nth_opt ty_args_for_expected i with
        | Some (Tdummy _) | None ->
          (* A [Tdummy] here means extraction couldn't statically reduce this
             type argument (e.g. a [prod]'s component type inferred through a
             non-reducible dependent [match] like [nt_semty x] at a literal
             [x], which is dependently well-typed in Coq but whose component
             types the ML type annotation on this specific node leaves as
             placeholders) -- it carries no more information than [None], so
             fall back the same way: to the concrete field type when the
             enclosing constructor has an erased ML type (e.g. pair(pred,
             action) with Tmeta{None}).  Combined with the MLlam
             Tarr-stripping logic, this lets gen_ctor_call recover the
             concrete element type for nil constructors, and lets a "cons"
             argument like a tuple literal's own component recover its
             declared field type so it gets any_cast'd to the concrete type
             instead of staying a bare [std::any] mismatched with the
             constructor's own (correctly concrete) return type. *)
          List.nth_opt field_types_for_wrap i
        | Some _ as x -> x
      in
      (* Propagate the erased-return-slot context into nested pair/tuple
         fields (e.g. the second component of [(n, (n, tt))]) so that a
         nested prod-cons also self-boxes its OWN components into
         [std::any] instead of relying on the outer cons to wrap the whole
         nested value as a single opaque [std::any].  Without this, only
         the outer level is erased and a further destructure of the inner
         value (e.g. a recursive call peeling one field at a time) hits a
         [std::any] holding a concrete (non-any) pair, causing
         [any_cast<pair<any,any>>] to throw at runtime. *)
      let is_list_cons_ctor_for_flow_pre =
        match r with
        | GlobRef.ConstructRef ((kn, _), _) ->
          let ind = GlobRef.IndRef (kn, 0) in
          Ml_type_util.is_custom_list_global ind
        | _ -> false
      in
      let propagate_erased_ctx =
        (not is_list_cons_ctor_for_flow_pre)
        &&
        match saved_ret with
        | Some t -> resolves_to_any_type t
        | None -> false
      in
      let erased_fn_slot, result =
        with_cpp_return_type (if propagate_erased_ctx then Some Tany else None)
        @@ fun () ->
      let expected_cpp_ty =
        match new_expected with
        | Some ml_ty ->
          let cpp_ty = cpp_of_ml env ml_ty in
          (* A field at a type parameter is the constructor's instantiation
             there, as the destination refined it: the annotation's own
             spelling erases a class variable with no instance in scope
             ([pair<std::any, ...>]) that the destination writes ([St<ptr>]),
             and a nested constructor built at the erased one boxes it. *)
          let cpp_ty =
            match List.nth_opt field_types_for_wrap i with
            | Some (Miniml.Tvar (_, j)) when Ml_type_util.has_tany_written cpp_ty -> (
              match List.nth_opt ctor_temps_at_slot (j - 1) with
              | Some t when not (prints_as_any t) ->
                Ml_type_util.refine_erased_by ~expected:t cpp_ty
              | _ -> cpp_ty )
            | _ -> cpp_ty
          in
          if prints_as_any cpp_ty then None
          else (match cpp_ty with
            | Tglob (g, _, _) when is_list_global g -> None
            | _ -> Some cpp_ty)
        | None -> None
      in
      let will_erase_fn_wrap =
        match List.nth_opt field_types_for_wrap i with
        | Some (Miniml.Tvar (_, j)) ->
          (match List.nth_opt ctor_temps_at_slot (j - 1) with
          | _ when is_passthrough_ctor_arg i -> false
          | Some t when prints_as_any (unfold_cpp_typedef env t) ->
            ml_expr_is_function_value e
          | _ -> false)
        | _ -> false
      in
      let e =
        if will_erase_fn_wrap then
          match strip_magic e with
          | MLlam (id, ty, body) ->
            (* The lambda is stored via [crane_erase_fn] into an erased slot,
               so at runtime it is invoked with its argument boxed as a single
               [std::any] holding the fully-erased representation
               ([pair<any,any>] for a pair domain) — that is what producers of
               a value-dependent type emit (see [deep_erase]).  Its
               parameter's own pattern match must therefore treat the scrutinee
               as erased and go through [any_cast<pair<any,any>>]. *)
            let param_cpp_ty = cpp_of_ml env ty in
            if Ml_type_util.has_tany_in_type param_cpp_ty then
              MLlam (id, ty, mark_own_param_for_pair_erasure 1 body)
            else
              (* Domain resolves to a fully concrete type at this literal (e.g.
                 a literal index [0] picks out a concrete branch of a dependent
                 type family), yet the value received at runtime is the erased
                 [pair<any,any>] a generic producer emits.  Erase the parameter
                 to [std::any] so the lambda renders with an erased parameter
                 and the [any_cast<pair<any,any>>] on it compiles. *)
              MLlam (id, Miniml.Tunknown, mark_own_param_for_pair_erasure 1 body)
          | _ -> e
        else e
      in
      (* The slot's own signature, when it erased only its domain: a callable
         reaching it is written against that signature (its parameters arrive
         boxed), and {!coerce} adapts it with [crane_erase_fn]. *)
      let erased_fn_slot =
        if is_passthrough_ctor_arg i || not (ml_expr_is_function_value e) then
          None
        else
          match List.nth_opt field_types_for_wrap i with
          | Some (Miniml.Tvar (_, j)) -> (
            match
              Option.map Ml_type_util.tvar_erase_type
                (List.nth_opt ctor_temps_at_slot (j - 1))
            with
            | Some t when partially_erased_fun_ty t -> Some t
            | _ -> None )
          | _ -> None
      in
      let result =
        gen_ctor_arg
          ?expected_ty:
            ( match erased_fn_slot with
            | Some _ as t -> t
            | None -> expected_cpp_ty )
          ~slot:{slot with expected_ml_ty = new_expected} e
      in
      (erased_fn_slot, result)
      in

      (* Where this argument is stored, as far as its representation goes:
         [Some Tany] when the slot is erased and the value has to be boxed
         into it, [None] when it is stored as itself. *)
      let field_slot =
        (* A pass-through constructor (registered as ["%a0"]) has no field
           storage at all -- the argument is forwarded verbatim, so there is
           nothing to box into. *)
        if is_passthrough_ctor_arg i then None
        else
          match List.nth_opt field_types_for_wrap i with
          | Some (Miniml.Tvar (_, j)) ->
            ( match List.nth_opt ctor_temps_at_slot (j - 1) with
              (* The slot's real type may be a value-dependent erased type's
                 own alias (e.g. [pred_ty = crane::obj]) rather than the bare
                 [Tany] node, so unfold it before comparing -- otherwise a
                 function value stored there is never boxed at all, and the
                 declaration's constraint on the callable (still stated
                 against its concrete, un-erased signature) never gets
                 dropped either. *)
              | Some t when prints_as_any (unfold_cpp_typedef env t) ->
                ( match result with
                  (* A lambda that is not a function value is a generated IIFE,
                     not a callable being stored. *)
                  | CPPlambda _ when not (ml_expr_is_function_value e) -> None
                  | _ -> Some Tany )
              (* A slot that kept a concrete result but erased its domain
                 ([std::function<uint64_t(std::any)>], a pair component whose
                 Rocq type is [sty -> nat] at an erased [sty]) is not a box:
                 a callable reaches it through the [crane_erase_fn] adapter,
                 which {!coerce} supplies once it is told the slot's own
                 signature. *)
              | Some _ when erased_fn_slot <> None -> erased_fn_slot
              | Some _
                when slot_is_deeply_erased && not (slot_states_unboxed (j - 1))
                ->
                Some Tany
              | _ -> None )
          | _ -> None
      in
      let into =
        match field_slot with
        | Some _ as slot -> slot
        | None when slot.deep_erase ->
          (* This constructor names a concrete type for the field, so there is
             no erased slot to box into: the custom C++ form consumes the
             argument at that type.  [Ascii] is the clearest case -- its eight
             [bool] arguments are folded into a [static_cast<char>] bitmask, and
             a [std::any] is not contextually convertible to [bool].  A
             recursive field ([Tglob] naming the constructor's own inductive) is
             the same situation. *)
          let field_is_concrete =
            match List.nth_opt field_types_for_wrap i with
            | Some (Miniml.Tglob _ as ft) -> not (prints_as_any (cpp_of_ml env ft))
            | _ -> false
          in
          (* Don't box when building a custom LIST cons whose element cpp type
             is itself a container (e.g. [pair<any,any>]).  Storing it directly
             in [deque<pair<any,any>>] keeps element types consistent with what
             [gen_match_branch] expects via [erase_type_to_any].  Only for LIST
             cons: pair/tuple fields must stay [std::any] so the consumer's
             [any_cast<pair<any,any>>] works. *)
          let is_already_container =
            is_list_cons_ctor
            &&
            match new_expected with
            | Some ml_fty ->
              ( match cpp_of_ml env ml_fty with
                | Tglob (_, _ :: _, _) -> true
                | _ -> false )
            | None -> false
          in
          if field_is_concrete || is_already_container then None else Some Tany
        | None -> None
      in
      let result =
        match into with
        | Some into -> coerce ~term:e ~into result
        | None -> result
      in
      result) ts)
  in
  (* Helper to wrap expression in function call syntax if it has arguments.
     [yields] is the constructed value's C++ type, where the caller could work
     it out: a custom constructor is still a value of its inductive, so
     recording it here is what lets a consumer -- a loopification frame field,
     say -- name the type instead of falling back on [decltype]. *)
  let app ?yields x =
    match args with
    | [] -> x
    | _ ->
      CPPfun_call
        (Minicpp.call_sig ?yields ~nargs:(List.length args) (), x,
         of_reversed args)
  in
  (* When [ty] (the MLcons node's own type annotation) is not itself a
     resolved [Tglob] — e.g. an unresolved [Tmeta {contents = None}], which
     happens for a "cons" expression built from destructured pattern
     variables whose types extraction failed to unify with a non-reducible
     dependent computation (see [recover_pattern_var_types_from_scrutinee])
     — fall back to [ty_args_for_expected], already computed above via
     [deep_resolve]/[expected_ml_ty] for the very same
     purpose (recovering nil's element type in a pair).  Without this, a
     "cons" production whose own return type stayed unresolved loses its
     [list] template argument entirely, so [cpp_print.ml] can't substitute
     the generic [cons : A -> list A -> list A] schema's [Tvar]s and
     defaults them to [std::any] — producing [deque<any>] instead of the
     canonical erased [deque<pair<any,any>>] that the sibling "nil"
     production (whose literal, non-destructured type annotation IS
     resolved) emits, causing an [any_cast] shape mismatch at runtime. *)
  let ty =
    match ty with
    (* Resolved, but resolved to the producer's own erased instantiation: the
       closure stored in a [rose (option (nat -> nat))] left its arrow's metas
       unresolved, so the node would be built at [rose<optional<function<any
       (any)>>>] while the consumer names the concrete one.  The slot's
       arguments -- which is what [ty_args_for_expected] already merges in --
       are the ones both sides agree on. *)
    | Miniml.Tglob (n, tys, sc)
      when List.length ty_args_for_expected = List.length tys
           && List.exists (ml_type_contains_erased ~in_arrows:true) tys ->
      Miniml.Tglob (n, ty_args_for_expected, sc)
    | Miniml.Tglob _ -> ty
    | _ when ty_args_for_expected <> [] ->
      ( match r with
      | GlobRef.ConstructRef ((kn, i), _) ->
        Miniml.Tglob (GlobRef.IndRef (kn, i), ty_args_for_expected, [])
      | _ -> ty )
    | _ -> ty
  in
  let result =
    match ty with
    | Miniml.Tglob (n, tys, _) ->
      (* Step 1: Filter out index type args - only keep parameters.

         Inductive types distinguish between parameters (uniform across all
         constructors, e.g., the [A] in [list A]) and indices (may vary,
         e.g., the [n] in [vec A n]). In C++, only parameters become template
         arguments; indices are encoded in types or runtime values.

         We use [get_ind_num_param_vars_opt] to find the parameter count and
         [safe_firstn] to extract them. [safe_firstn] handles cases where the
         type arg list is shorter than expected (e.g., due to Tdummy Ktype
         erasure in make_tyargs). *)
      let tys =
        match n with
        | GlobRef.IndRef (kn, _) ->
          ( match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars ->
            (* Take first num_param_vars elements, or fewer if list is short *)
            safe_firstn num_param_vars tys
          | None ->
            (* Not in table - keep all type args *)
            tys )
        | _ ->
          (* Not an inductive ref - keep all type args *)
          tys
      in
      (* Step 2: Convert ML types to C++ types.  The enclosing type-variable
         names matter: inside a member template a [Tvar] is one of the
         method's own parameters ([_A0]), not an anonymous [T2].  The
         arguments instantiate an {i inductive's} parameters, so a stored
         function type keeps the flat arity its declaration is written at
         ([~curry:false]); currying here would make the instantiation
         disagree with the type the declaration spells. *)
      let temps = template_params_of_ml ~curry:false env tys in
      let temps = filter_erased_type_args temps in
      let temps = ind_promoted_type_args n @ temps in
      (* Step 2b: Recover type args from the return type when unresolved metas
         caused all type args to be erased.  This happens for nullary custom
         constructors (e.g., None) inside let-bindings: the extraction phase
         uses a fresh meta as the expected type, so the constructor's type
         parameter meta never gets unified with the concrete type.  If the
         enclosing function/constant return type matches the same inductive,
         extract the type args from there. *)
      let temps =
        if temps = [] && tys <> []
        then
          let from_expected =
            match slot.expected_ml_ty with
            | Some (Miniml.Tglob (exp_r, exp_tys, _))
              when Names.GlobRef.CanOrd.equal exp_r n
                   && List.length exp_tys = List.length tys ->
              let exp_temps = build_template_params env [] exp_tys in
              let r = filter_erased_type_args exp_temps in
              if r <> [] && not (List.exists (function Tvar (Tv_index (_, None)) -> true | _ -> false) r)
              then r
              else []
            | _ -> []
          in
          if from_expected <> [] then from_expected
          else
            let from_ret =
              match (!tctx).current_cpp_return_type with
              | Some (Minicpp.Tglob (ret_r, ret_tys, _))
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length tys ->
                filter_erased_type_args ret_tys
              | Some (Minicpp.Tshared_ptr (Minicpp.Tglob (ret_r, ret_tys, _)))
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length tys ->
                filter_erased_type_args ret_tys
              | _ -> []
            in
            if from_ret <> [] then from_ret
            else if (!tctx).promoted_var_map <> [] then
              Option.default temps (promoted_tys_of_arity (List.length tys))
            else temps
        else temps
      in
      (* For custom list constructors (e.g., deque nil/cons), a container
         element type built entirely from [Tdummy] placeholders (extraction's
         "no information available" marker, e.g. because the production's
         return type is an opaque, non-reducible alias like [symbol_semty])
         carries no genuine field information.  A sibling production for the
         SAME Coq list type may still see concrete structure here (e.g. a
         literal, directly-annotated [list (string*nat)]); preserving that
         structure as [pair<any,any>] while the other production collapses
         to bare [std::any] would produce two incompatible container shapes
         for the same runtime list, causing an [any_cast] mismatch at the
         consumer.  Collapse to bare [std::any] whenever the container is
         hollow, regardless of [deep_erase], so nil/cons always
         agree on representation. *)
      let is_custom_list =
        match r with
        | GlobRef.ConstructRef ((kn, _), _) ->
          let ind = GlobRef.IndRef (kn, 0) in
          Ml_type_util.is_custom_list_global ind
        | _ -> false
      in
      let rec ml_ty_all_dummy = function
        | Tdummy _ -> true
        | Tglob (_, (_ :: _ as args), _) -> List.for_all ml_ty_all_dummy args
        | Tmeta {contents = Some t} -> ml_ty_all_dummy t
        | _ -> false
      in
      (* [hollow_container] fires when the list's ML element annotation is all
         [Tdummy] (extraction couldn't reduce it, e.g. an opaque alias like
         [symbol_semty]).  Collapsing to bare [std::any] is only correct when
         the concrete C++ element type ([temps]) is ITSELF erased — i.e. a
         sibling production for the same erased list would build [deque<any>]
         and the two must agree.  When [temps] recovers a fully-concrete
         element type despite the hollow ML annotation (e.g. an abstract
         [frame] seen through a module type, which still resolves to the
         concrete [typename D::Defs::frame]), the list is a genuine
         [deque<frame>] flowing into a concretely-typed consumer, so the
         concrete element type must be preserved. *)
      let hollow_container =
        is_custom_list && List.exists ml_ty_all_dummy tys
        && List.exists Ml_type_util.has_erased_type_in_type temps
      in
      let temps =
        if hollow_container && temps <> [] then
          List.map (fun _ -> Tany) temps
        else if slot.deep_erase && temps <> [] then
          (* Canonical erased shape for a list is [deque<std::any>] -- a bare
             [std::any] per element, not a structure-preserving
             [deque<pair<any,any>>].  A sibling production for the same Coq
             list type (e.g. one built via a different code path that already
             collapses to the flat shape) must agree exactly, or the
             consumer's [any_cast] throws [std::bad_any_cast] at runtime.
             See the matching invariant in [gen_expr]'s [MLrel]/[MLmagic]
             cases. *)
          List.map (fun _ -> Tany) temps
        else temps
      in
      let temps = if temps = [] then type_args_at_carrier n else temps in
      let value_ty = Tglob (n, temps, []) in
      app ~yields:value_ty (mk_cppglob ~yields:value_ty r temps)
    | _ ->
      (* Type is not a Tglob - no type args to pass.
         This case is rare for custom constructors, which typically have
         Tglob types. Fall back to bare constructor reference. *)
      app (mk_cppglob r (type_args_at_carrier r))
  in
  result
  in
  (* Collapse identity inline customs (%a0) for constructors, matching
     the same collapse done for function applications at gen_expr. *)
  let result =
    match result with
    | CPPfun_call (_, CPPglob (_, _, Some ci), {rev = [single_arg]})
      when inline_shape ci = Some Inline_identity ->
      single_arg
    | _ -> result
  in
  result

(** Generate C++ expression from ML AST. Main expression compiler - handles
    lambdas, applications, constructors, pattern matching, etc. Monadic
    non-function globals are wrapped in CPPfun_call by the MLglob case below.

    [deep_erase] says that [ml_e] flows into a slot that is really
    [std::any], so any constructor it builds has to use the canonical erased
    shape: every producer of the same Coq type must agree with the fixed
    [any_cast] that reads it back.  A "cons" production keeping
    [deque<Prod<Nat, Nat>>] where the matching "nil" erased to
    [deque<Prod<any, any>>] is what [std::bad_any_cast] at the consumer looks
    like.

    Only constructors read it, but the slot is a property of the whole
    subterm, so it is carried down every position whose value ends up in that
    slot -- an argument, a coercion's operand, a branch result, a tail
    expression, the body of a lambda that is itself the stored value.  A
    position that opens a new slot (a let-bound right-hand side, a
    non-tail statement) does not take it. *)
and gen_expr ?(expected_ty : cpp_type option) ?(slot = empty_slot) env
    (ml_e : ml_ast) : cpp_expr =
  match ml_e with
  | MLrel i ->
    let var_expr =
      try CPPvar (get_db_name i env)
      with Failure _ -> CPPvar (db_fallback_id i)
    in
    (* Phase 2: move on last use. Emit std::move if: (1) the variable is dead
       after this point, (2) it's an owned variable (not borrowed), and (3) this
       is its only occurrence in the current RHS expression.
       Never move a typeclass instance -- it is a type reference in the concept
       paradigm, not an owned value, and wrapping it produces invalid C++ like
       [std::move(_tcI0)::method()].  Recognised by identity rather than by ML
       type: this binder is synthesised by {!Common.tc_instance_id}, and inside
       a generated instance method it is a template parameter of the enclosing
       struct, with no entry of its own in [env_types]. *)
    let is_tc_param =
      match var_expr with CPPvar id -> Common.is_tc_instance_id id | _ -> false
    in
    let move_candidate =
      (not is_tc_param)
      && Escape.IntSet.mem i (!tctx).move_dead_after
      && Escape.IntSet.mem i (!tctx).move_owned_vars
    in
    let result = if move_candidate then CPPmove var_expr else var_expr in
    if binder_is_boxed i then begin
      match expected_ty with
      | Some ty when not (prints_as_any ty) && ty <> Tvoid ->
        if resolves_to_any_type ty then result
        else
          (* For a CUSTOM-LIST container target, the erased var is boxed at
             runtime as [deque<...erased...>] (each element fully erased).  A
             direct [any_cast] to the concrete-element container
             ([deque<pair<string,Val>>]) would implicitly re-box the already-
             unwrapped erased container into a fresh [std::any] and then throw
             at runtime, since that any holds a [deque<pair<any,any>>].  Unwrap
             to the ERASED container instead; a downstream consumer that needs
             the concrete-element container (a constructor field via
             [crane_container_cast], or [eta_fun]'s function-argument path)
             converts it.  Scalar targets keep the direct concrete [any_cast]. *)
          (* Does [ty] denote a list container, possibly under a [Tnamespace]
             wrapper?  (A namespaced list — e.g. a functor-qualified
             [Datatypes::List] — must be recognized too, otherwise the fallback
             below emits the target verbatim and leaks an abstract/unresolved
             element type variable, e.g. [any_cast<List<T1>>], inside an erased
             [crane_erase_fn] body which is not a template context.) *)
          let rec ty_is_list = function
            | Tnamespace (_, t) -> ty_is_list t
            | Tglob (g, _ :: _, _) -> is_list_global g
            | _ -> false
          in
          if ty_is_list ty then
             (* Canonical erased shape is [deque<std::any>] -- every element
                boxed as a single [std::any] (see [gen_expr_custom_cons]'s
                hollow-container collapse for the producer side of this same
                invariant).  Erasing to [deque<pair<any,any>>] instead (i.e.
                preserving the element's own container structure) would
                disagree with that canonical shape: [crane_container_cast]
                (the consumer this cast feeds) expects a plain [std::any] per
                element so it can unbox each one with [crane_any_cast]
                directly; handing it a [pair<any,any>] element instead makes
                it implicitly re-box that pair into a fresh [std::any] before
                [crane_any_cast] can recover it, which is redundant with (and,
                if the destination shape or printer state ever disagrees,
                incompatible with) the direct-[std::any]-per-element path. *)
             let rec erase_list_elems = function
               | Tnamespace (ns_g, t) -> Tnamespace (ns_g, erase_list_elems t)
               | Tglob (g, args, ns) -> Tglob (g, List.map (fun _ -> Tany) args, ns)
               | t -> t
             in
             Cpp_erasure.unbox (erase_list_elems ty) result
           else Cpp_erasure.unbox ty result
      | _ -> result
    end
    else result
  (* A singleton class's dictionary applied, which is the body of the class's
     projection: the method, called on the instance -- a template parameter,
     so a static member -- at the method's own type variables, which here are
     the projection's, numbered past the class's parameters. *)
  | MLapp (head, args) when singleton_dictionary env head <> None ->
    let inst, class_ref, method_ref = Option.get (singleton_dictionary env head) in
    let ipv = List.length (Table.get_ind_ip_vars class_ref) in
    let n_own = Ml_type_util.method_tvar_count class_ref (Table.find_type method_ref) in
    let tvars = get_current_type_vars () in
    let targs =
      List.init n_own (fun k ->
          convert_ml_type_to_cpp_type env tvars (Miniml.Tvar (Schematic, ipv + 1 + k)))
    in
    let value_args = List.filter (function MLdummy _ -> false | _ -> true) args in
    mk_call
      (CPPscope (CPPvar inst, Common.id_of_global Term method_ref, targs))
      (List.map (gen_expr env) value_args)
  | MLapp (MLmagic (_, t), args) ->
    gen_expr ?expected_ty ~slot env (MLapp (t, args))
  | MLapp (((MLdummy _ | MLexn _) as absurd), _) ->
    (* Applying an absurd head — the eliminator of a branch that the indices
       rule out.  The application is itself unreachable, so emit the throw
       alone: calling it would apply the throwing thunk's [std::any] result
       as though it were a function. *)
    gen_expr ?expected_ty env absurd
  | MLapp (MLglob (r, ret_tys), a1 :: l) when is_ret r ->
    if (!tctx).itree_mode = Reified then begin
      (* Reified mode: Ret produces ITree<R>::ret(value). Don't strip it. *)
      Table.require_itree_header ();
      let t = Common.last (a1 :: l) in
      match t with
      | MLglob (g, _) when is_ghost g ->
        mk_itree_ret Tvoid []
      | _ ->
        let inner = gen_expr env t in
        (* Extract R from the monad's type arguments: itree has template "%t1"
           so the ML type args for Ret are [E, R] where E is typically Tdummy
           and R is the result type. *)
        let r_cpp =
          let non_dummy = filter_value_types ret_tys in
          match non_dummy with
          | r_ml :: _ ->
            cpp_of_ml env r_ml
          | [] -> Tvoid
        in
        mk_itree_ret r_cpp [inner]
    end
    else begin
      let t = Common.last (a1 :: l) in
      gen_expr env t
    end
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h -> gen_expr env
     (MLapp (a1, a2::[])) *)
  | MLapp (MLglob (r, _), _ :: _ :: _) as a when is_bind r
      && (!tctx).itree_mode <> Reified ->
    (* Sequential mode: bind in expression context (e.g., nested inside
       another expression). Wrap in IIFE so gen_stmts can sequentialize. *)
    with_escape_analysis (fun () ->
      mk_iife None (gen_stmts env (fun x -> Sreturn (Some x)) a) )
  | MLapp (MLfix _, _) as a ->
    (* Nested fix application in expression context (e.g., S((fix aux ...) es)).
       Wrap in an IIFE, delegating to gen_stmts which handles MLapp(MLfix
       ...). *)
    with_escape_analysis (fun () ->
      mk_iife None (gen_stmts env (fun x -> Sreturn (Some x)) a) )
  | MLapp (MLapp ((MLglob _ as g), inner_args), outer_args) ->
    (* Flatten nested MLapp when inner callee is a global reference. This arises
       from Rocq partial applications like: div_conq_split x f1 f2 l which
       extracts as MLapp(MLapp(MLglob(dcs), [x,f1,f2]), [l]). Flattening to
       MLapp(MLglob(dcs), [x,f1,f2,l]) lets eta_fun see the complete argument
       list and generate a direct call. *)
    gen_expr ?expected_ty ~slot env (MLapp (g, inner_args @ outer_args))
  | MLapp (MLglob (r, _), [arg]) when Table.is_numeral_converter r ->
    (* Fold Number.uint/signed_int digit chain into a direct integer literal.
       Tries unsigned (of_num_uint) then signed (of_num_int).
       Falls through to eta_fun on failure. *)
    let ind_ref = Option.get (Table.numeral_ind_of_converter r) in
    ( match Table.get_numeral_info ind_ref with
    | Some info ->
      let folded = match try_fold_num_uint arg with
        | Some _ as r -> r
        | None -> try_fold_num_int arg
      in
      ( match folded with
      | Some n ->
        render_numeral info n
      | None -> eta_fun env (MLglob (r, [])) [arg] )
    | None -> eta_fun env (MLglob (r, [])) [arg] )
  | MLapp (MLcase (typ, scrut, pv), outer_args) when Array.length pv = 1 ->
    (* Flatten outer args into a single-branch case body.  A case with one
       branch is a destructuring and nothing else, whatever it scrutinises --
       a record, a pair, any one-constructor inductive -- so applying its
       result is applying the branch body.
       When a typeclass method is partially applied, Rocq extracts it as
       MLcase(instance, [(binds, MLapp(MLrel field, inner_args))]). If this
       MLcase is the callee of an outer MLapp, the inner call only has some
       args while the outer provides the rest — generating a curried C++ call
       like make(a)(b) instead of make(a, b).  Push the outer args into the
       branch body so gen_expr sees the complete argument list. *)
    let (ids, rty, pat, body) = pv.(0) in
    let n_bindings = List.length ids in
    let lifted_outer = List.map (ast_lift n_bindings) outer_args in
    let new_body = match body with
      | MLapp (f, inner_args) -> MLapp (f, inner_args @ lifted_outer)
      | _ -> MLapp (body, lifted_outer)
    in
    gen_expr ~slot env (MLcase (typ, scrut, [|(ids, rty, pat, new_body)|]))
  (* A class field is projected through the instance wherever the instance
     survived, whatever mapping the field carries -- see
     {!static_projection_instance}. *)
  | MLapp (MLglob (x, tys), args) when static_projection_instance env x args <> None -> (
    let inst = Option.get (static_projection_instance env x args) in
    match static_projection_missing env x tys args inst with
    | [] -> project_through_instance env x tys args inst
    | missing ->
      let k = List.length missing in
      let call =
        MLapp
          ( MLglob (x, tys),
            List.map (Mlutil.ast_lift k) args @ List.init k (fun i -> MLrel (k - i)) )
      in
      gen_expr ?expected_ty ~slot env
        (Mlutil.named_lams
           (List.rev (List.mapi (fun i t -> (Id (Id.of_string ("a" ^ string_of_int i)), t)) missing))
           call ) )
  | MLapp (f, args) ->
    (* A partial application is a callable this position may expect at a
       different currying than the callee's own arrows give it, so the slot's
       type travels with it. *)
    let result = eta_fun ?expected_ty ~slot env f args in
    (* A callee whose result is only pinned down by a type index hands back a
       [std::any] (see {!result_is_index_only_tvar}); recover it at the type
       this position expects. *)
    let callee_ty =
      match f with
      | MLglob (r, _) -> find_type_opt r
      | MLrel i -> get_env_type_opt i
      | _ -> None
    in
    (* The same type, at the instantiation this call uses: what the call
       yields is the codomain of *that*, not of the general scheme. *)
    let callee_ty_inst =
      match (f, callee_ty) with
      | MLglob (id, tys), Some ty ->
        let value_args =
          List.filter (function MLdummy _ -> false | _ -> true) args
        in
        Some (instantiate_at_call id tys value_args ty)
      | _ -> callee_ty
    in
    (* A callee typed by a function alias ([church]) hands back whatever the
       alias's codomain erased to; the alias is the only place that says so,
       since the term itself carries no arrows. *)
    let alias_result_is_boxed ty =
      match ty with
      | Miniml.Tglob (GlobRef.ConstRef _, _, _) ->
        ( match expand_ml_fun_alias ty with
        | Miniml.Tarr _ as expanded ->
          ( match ml_codomain expanded with
          | Miniml.Tvar (_, _) | Miniml.Tunknown -> true
          | _ -> false )
        | _ -> false )
      | _ -> false
    in
    (* A binder whose declared C++ type boxes its result -- a rank-2 parameter
       typed [std::function<std::any(std::any)>], say -- hands back a box
       however the term's ML type reads.  The assignment made where the binder
       was bound is the authority on that; only a saturated call reaches the
       codomain it names. *)
    let binder_result_is_boxed =
      match f with
      | MLrel i ->
        ( match
            Option.map
              (fun t -> unfold_cpp_typedef env (strip_cpp_ref_const t))
              (binder_cpp_type_or_derive env i)
          with
        | Some (Tfun (doms, cod)) ->
          let n_runtime =
            List.length
              (List.filter (fun a -> not (Mlutil.isMLdummy (strip_magic a))) args)
          in
          prints_as_any cod && List.length doms = n_runtime
        | _ -> false )
      | _ -> false
    in
    (* Nor can a global whose declaration boxed its result -- [id] declared
       at [crane::obj] -- hand back anything else, however this call
       instantiates it. *)
    let declared_result_is_boxed =
      match f with MLglob (r, _) -> glob_declared_cod_erases r | _ -> false
    in
    let result =
      if
        binder_result_is_boxed || declared_result_is_boxed
        || ( match callee_ty with
           | Some ty -> result_is_index_only_tvar ty || alias_result_is_boxed ty
           | None -> false )
      then unbox_into expected_ty result
      else result
    in
    record_call_sig env callee_ty_inst result
  | MLlam _ as a ->
    (* Where the slot is a definitional class -- an alias for a function
       type -- which of its domains the declaration takes as values.  Read
       off the alias's own definition, before this call instantiated it:
       [Id_ obj C] is [forall a : obj, C a a], a function of an object, and
       stays one when [obj := Type -> Type] erases the object; [MonadIter m]
       is [forall R I : Type, ...], and takes [R] and [I] as types only. *)
    let slot_value_doms =
      let rec alias_ref t =
        match strip_param_spelling t with
        | Tnamespace (_, t) -> alias_ref t
        | Tglob (GlobRef.ConstRef kn, _, _) -> Some kn
        | _ -> None
      in
      let rec value_doms t =
        match resolve_tmeta (expand_ml_fun_alias t) with
        | Miniml.Tarr (d, c) -> not (Mlutil.isTdummy (resolve_tmeta d)) :: value_doms c
        | _ -> []
      in
      match Option.bind expected_ty alias_ref with
      | Some kn -> (
        match Table.lookup_typedef_unchecked kn with
        | Some body -> value_doms body
        | None -> [] )
      | None -> []
    in
    (* Whether binder [i] of [binders] (innermost-first, over [body]) becomes
       a C++ parameter.  A binder typed [Tdummy] carries nothing, unless the
       body names it or the slot's declaration takes a value at its position
       ([slot_value_doms]): [Cat IFun]'s [cat] binds objects [a b c] that
       [obj := Type -> Type] erases, and [Cat] is a function of them all the
       same.  A binder with no type ([Taxiom]) is one erasure took the type
       from -- [IFun]'s [forall T] -- and unused it is erased like a dummy.
       The count of binders the term writes and the parameter list it is
       written with are both read off this, so they cannot disagree. *)
    (* ... and only where the slot's own domain there is a box: an erased
       binder stands for an erased value, [Id_]'s object, never for the
       [Nat] state a [stateT] takes first. *)
    let slot_doms_cpp =
      match Option.map (unfold_cpp_typedef env) expected_ty with
      | Some (Tfun (doms, _)) -> doms
      | _ -> []
    in
    let slot_keeps binders i =
      let d = List.length binders - 1 - i in
      match List.nth_opt slot_value_doms d with
      | Some true -> (
        match List.nth_opt slot_doms_cpp d with
        | Some t -> prints_as_any t
        | None -> true )
      | _ -> false
    in
    let binder_emitted ~body binders i ty =
      slot_keeps binders i
      || ((not (isTdummy ty)) && ty <> Miniml.Taxiom && not (ml_type_is_void ty))
      || Mlutil.ast_occurs (i + 1) body
    in
    (* A slot spelled [std::type_identity_t<Id_<...>>] -- a definitional
       class, taken out of deduction -- is still a function type, and the
       lambda is written against it: its arity and its result. *)
    let expected_ty =
      let rec as_fun t =
        match t with
        | Tnondeduced t' -> as_fun t'
        | Tconst t' | Tref (Lvalue, t') -> as_fun t'
        | Tfun _ -> Some t
        | t -> (
          match unfold_cpp_typedef env t with
          | Tfun _ as f when f <> t -> Some f
          | _ -> None )
      in
      match expected_ty with
      | Some t -> ( match as_fun t with Some f -> Some f | None -> expected_ty )
      | None -> None
    in
    let args, a = collect_lams a in
    (* Nested binders normally flatten into one multi-parameter C++ lambda.
       That is wrong when the context expects a curried function whose result
       is itself a function -- e.g. an [endo (nat -> nat)] field of type
       [std::function<F(F)>] with [F = std::function<uint64_t(uint64_t)>].
       Keep only the binders the expected type takes and let the remainder
       become the closure it returns. *)
    let args, a =
      let rec fun_ty_of = function
        | Tconst t | Tref (_, t) -> fun_ty_of t
        | Tfun (dom, cod) -> Some (List.length dom, cod)
        | _ -> None
      in
      let is_runtime_binder (_, ty) =
        (not (isTdummy ty)) && not (ml_type_is_void ty)
      in
      let split_after_runtime n binders =
        (* Prefix of [binders] holding exactly [n] runtime binders, or [None]
           if there are no more than [n] of them. *)
        let rec go seen acc = function
          | [] -> None
          | b :: rest ->
            let seen = if is_runtime_binder b then seen + 1 else seen in
            if seen > n then Some (List.rev acc, b :: rest)
            else go seen (b :: acc) rest
        in
        go 0 [] binders
      in
      (* Binders the expected type takes that the term does not write: the
         body is a function value, and the context wants its parameters in
         this lambda's own list rather than in a closure it returns.  Under-
         applied calls are eta-expanded too, but at the C++ level and after
         this lambda has been built, so the synthesised parameter lands
         {e inside} it -- [pair -> (list -> list)] where the consumer takes
         [(pair, list) -> list].  Writing the missing binders here instead
         makes the body a saturated call, so that expansion never fires.

         The binders are given no ML type on purpose: the derivation below
         reads an erased parameter's type out of [expected_ty]'s domain at
         the same index, which is the only place that says what it is. *)
      (* [extend n] -- the binders the expected signature takes that the term
         does not write, or [None] where there are none worth writing.

         Each test below has to run only once the ones before it have passed:
         the count decides whether anything is missing at all, and the later
         ones index the last [k] domains, which is not a meaningful range
         until [k] is known to be positive.  Written as nested [if]s rather
         than one condition for that reason -- OCaml's [let] is strict, so a
         guard placed after the computation it guards never runs. *)
      let extend n =
        (* Count the binders that will be {e emitted}, on the same terms the
           parameter list below is filtered: a binder whose recorded type is
           dummy is still a parameter where the body names it. *)
        let emitted_binder i (_, ty) = binder_emitted ~body:a args i ty in
        let k =
          n - List.length (List.filteri (fun i b -> emitted_binder i b) args)
        in
        if k < 0 then
          (* The term writes {e more} binders than the signature declares.
             Nothing is missing, and the surplus is not this function's
             business: a slot typed [std::function<T(U)>] against a
             two-binder lambda is an ordinary curried result, which the
             [split_after_runtime] branch above handles where the codomain
             says so. *)
          None
        else if k = 0 then None
        else if
          (* The expected C++ arity has to be backed by the same number of ML
             domains that genuinely carry a value.  A reified tree's
             continuation is typed [unit -> itree ...] and takes one
             [std::monostate]: the value carries nothing but the slot is real,
             so the binder counts like any other. *)
          let real ty = is_runtime_binder ((), ty) in
          let rec leading i ty =
            i = 0
            ||
            match resolve_tmeta ty with
            | Miniml.Tarr (a, b) -> real a && leading (i - 1) b
            | _ -> false
          in
          not (match slot.expected_ml_ty with Some ty -> leading n ty | None -> false)
        then None
        else if
          (* A binder is only worth writing if the slot says what it is.  The
             synthesised ones are the last [k] of the expected signature's
             domains, and each has to be a type this lambda could be written
             against: spelled with no erased position anywhere in it, and
             naming no type variable out of scope here (the same condition
             {!slot_param_cpp_ty} imposes, and for the same reason).  Where it
             is not, the parameter would be declared [const auto &] or
             [std::any] -- an untyped parameter the consumer cannot resolve,
             which is worse than the closure the term already returns, and
             which would also displace the C++-level expansions that do have
             types to work from. *)
          not
            ( match Option.map (unfold_cpp_typedef env) expected_ty with
            | Some (Tfun (doms, _)) when List.length doms = n ->
              let tvars = get_current_type_vars () in
              List.for_all
                (fun i ->
                  match List.nth_opt doms i with
                  | Some t ->
                    (not (Ml_type_util.has_tany_written t))
                    && Id.Set.for_all
                         (fun nm -> List.exists (Id.equal nm) tvars)
                         (Minicpp.tvar_names t)
                  | None -> false )
                (List.init k (fun i -> n - k + i))
            | _ -> false )
        then None
        else
          let fresh =
            List.init k (fun i ->
                ( Miniml.Tmp (Id.of_string (Printf.sprintf "_eta%d" (k - 1 - i))),
                  Miniml.Tunknown ) )
          in
          Some
            ( fresh @ args,
              MLapp (ast_lift k a, List.init k (fun i -> MLrel (k - i))) )
      in
      match Option.bind expected_ty fun_ty_of with
      | Some (n, cod) when n > 0 && fun_ty_of cod <> None ->
        (* [collect_lams] yields binders innermost-first; the ones to keep are
           the outermost [n]. *)
        ( match split_after_runtime n (List.rev args) with
        | Some (kept, inner) ->
          ( List.rev kept,
            List.fold_left
              (fun b (x, ty) -> MLlam (x, ty, b))
              a (List.rev inner) )
        | None -> ( match extend n with Some r -> r | None -> (args, a) ) )
      | Some (n, _) when n > 0 -> (
        match extend n with Some r -> r | None -> (args, a) )
      | _ -> (args, a)
    in
    (* A binder's recorded type is whatever extraction managed to infer for
       it, and a component it never inferred stays erased even where the rest
       of the type is spelled in full: [pair(list(pair(A, B)), Tdummy)] for a
       [x] the callee declares at [pair(list(pair(A, B)), list(B))].  The slot
       states the whole shape, so refine the binder against it -- here, at the
       {e ML} type, before anything reads it.

       Doing it here rather than on the C++ spelling is the point.  The
       signature and the body are generated from this one type: correct it at
       the declaration and the body decomposes the pair at the type it really
       has, while correcting the spelling alone leaves the body unboxing at the
       erased view its own generation assumed (see
       {!Ml_type_util.refine_param_from_slot}, which for that reason may only
       refine as far as still-erased).

       [args] is innermost-first and a signature's domains are in source order,
       so the two are indexed opposite ways. *)
    (* A variable of the callee's the slot names and this scope does not --
       [TFunctor_block]'s [U], its instance emitted at [std::any] -- is erased
       where it sits, so the rest of the slot still describes the lambda: its
       binders ([md : list (metadata _)], what the structured binding of a
       [List<metadata<std::any>>] holds) and its result. *)
    (* Only where extraction left the lambda's binders open is it read at the
       erased view: an erased position is no information about a binder that
       has a type of its own ([state_get]'s [s : T1]), nor about its result. *)
    let rec has_open_meta t =
      match t with
      | Miniml.Tmeta {contents = None} -> true
      | Miniml.Tmeta {contents = Some t} -> has_open_meta t
      | Miniml.Tarr (a, b) -> has_open_meta a || has_open_meta b
      | Miniml.Tglob (_, ts, _) -> List.exists has_open_meta ts
      | _ -> false
    in
    let binders_left_open = List.exists (fun (_, ty) -> has_open_meta ty) args in
    let rec erase_unscoped t =
      match resolve_tmeta t with
      | Miniml.Tvar _ as v when not (names_only_scoped_tvars (cpp_of_ml env v)) ->
        Miniml.Tunknown
      | Miniml.Tarr (a, b) -> Miniml.Tarr (erase_unscoped a, erase_unscoped b)
      | Miniml.Tglob (g, ts, l) -> Miniml.Tglob (g, List.map erase_unscoped ts, l)
      | t -> t
    in
    let args =
      match (slot.deep_erase, slot.expected_ml_ty) with
      | false, Some fn_ty ->
        let rec domains ty =
          match resolve_tmeta ty with
          | Miniml.Tarr (d, cod) -> d :: domains cod
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
              ( x,
                Ml_type_util.refine_erased
                  ~writable:(fun t -> names_only_scoped_tvars (cpp_of_ml env t))
                  ty d ) )
          args
      | _ -> args
    in
    let lam_params = List.map (fun (x, y) -> (id_of_mlid x, y)) args in
    let args, env = push_vars' lam_params env in
    let saved_env_types = (!tctx).env_types in
    push_binders env args;
    (* Infer owned/borrowed for each lambda parameter using escape analysis.

       Owned parameters (stored in a data structure or returned) are passed by
       value (shared_ptr<T>), transferring ownership to the callee.  Borrowed
       parameters (only read, not stored/returned) are passed by const ref
       (const shared_ptr<T>&), avoiding a refcount bump on every call.

       The inference is conservative: if a parameter escapes in any code path
       (e.g. captured by a closure, stored in a constructor, or returned), it
       is marked as owned.  See {!Escape.infer_owned_params}. *)
    let n_all_params = List.length lam_params in
    let owned_flags = infer_owned_flags n_all_params a args
    in
    let args_with_owned =
      List.map2 (fun (id, ty) owned -> (id, ty, owned)) args owned_flags
    in
    (* A binder typed [Tdummy] carries nothing, so it is not a C++ parameter.
       Unless the body names it: an
       instance method's body is read at the class's erased method type, where
       a value binder the class quantified over has no type left to record,
       and dropping it leaves the body naming a variable nothing declares.
       What the body does with a binder settles whether it is one; the
       recorded type only says so where there is nothing to go on. *)
    (* A reified tree's continuation is typed [unit -> itree ...] and its
       consumer invokes it with one [std::monostate], so the slot is real even
       though the value carries nothing.  For a named function the signature is
       written from the type and the parameter is there whether or not a binder
       was; a lambda's parameter list {e is} its binder list, so dropping the
       binder drops the parameter and the callable comes out nullary.  A
       reified [unit] binder is therefore kept -- as an ordinary unused
       parameter -- and only the genuinely absent types are filtered. *)
    let filtered_args_with_owned =
      List.filteri
        (fun i (_, ty, _) -> binder_emitted ~body:a args_with_owned i ty)
        args_with_owned
    in
    (* Each emitted binder's position among all of them, for the body's
       de Bruijn indices. *)
    let emitted_binder_indices =
      List.filteri
        (fun i _ ->
          let _, ty, _ = List.nth args_with_owned i in
          binder_emitted ~body:a args_with_owned i ty )
        (List.mapi (fun i _ -> i) args_with_owned)
    in
    let filtered_args =
      List.map (fun (id, ty, _) -> (id, ty)) filtered_args_with_owned
    in
    (* A lambda standing for a rank-2 argument -- [fun _ e => ...] for a
       parameter of type [forall X, E X -> M X] -- is handed a type the caller
       has not chosen yet.  Extraction leaves that type as [Tunknown], which
       prints as [std::any], and a lambda written against [std::any] is a
       claim the body cannot keep: it would have to name a concrete result
       where only the caller knows one.

       The honest spelling is a polymorphic function object: the erased
       positions become the lambda's own template parameter, so the parameter
       reads [const E<_X> &] and the body says [_X] where it would otherwise
       guess.  The callee recovers the result with [std::invoke_result_t]; see
       {!Gen_decls.relax_tt_applied_return}. *)
    let rank2_carrier =
      (* Only where the slot deduces the callback's type.  A slot that spells
         its own signature -- a [std::function<Nat(std::any)>] field, say --
         has already settled what the lambda is, and a polymorphic function
         object does not convert to it. *)
      let slot_declares_signature =
        match Option.map (unfold_cpp_typedef env) expected_ty with
        | Some (Tfun _) -> true
        | _ -> false
      in
      if
        (not slot_declares_signature)
        && List.exists
             (fun (_, ty, _) -> Rank2.quantifies_erased_type ty)
             filtered_args_with_owned
      then Some Rank2.carrier_name
      else None
    in
    let at_carrier ty =
      match rank2_carrier with None -> ty | Some x -> Rank2.at_carrier x ty
    in
    let f =
      with_escape_analysis (fun () ->
        let tvars = get_current_type_vars () in
        (* What the slot this lambda flows into declares its parameters to be,
           when it declares a signature at all. *)
        let expected_param_cpp_tys =
          match Option.map (unfold_cpp_typedef env) expected_ty with
          | Some (Tfun (doms, _)) -> Some doms
          | _ -> None
        in
        (* [filtered_args_with_owned] is innermost-first and the printer
           reverses it, while a slot's domain list is in source order, so a
           parameter's index into the two runs opposite ways. *)
        let n_emitted_params = List.length filtered_args_with_owned in
        let slot_dom j = n_emitted_params - 1 - j in
        let slot_dom_cpp_ty j =
          Option.bind expected_param_cpp_tys (fun doms ->
              List.nth_opt doms (slot_dom j) )
        in
        let tvar_in_scope n = List.exists (Id.equal n) tvars in
        let slot_param_cpp_ty j =
          (* Only a type this lambda could actually be written against.  The
             slot is read off the callee's declaration, so it may name that
             declaration's own template parameters, which are no more in scope
             here than the erasure was -- adopting one trades [std::any] for a
             free name. *)
          match slot_dom_cpp_ty j with
          | Some t
            when Id.Set.for_all tvar_in_scope (Minicpp.tvar_names t) ->
            Some t
          | _ -> None
        in
        (* Whether [body] takes its single binder apart: matches on it, or
           applies to it a projection spelled as member access (an inline
           custom [%a0.first]). *)
        let body_reads_members_of_binder body =
          let member_access g =
            Table.is_inline_custom g
            && ( match Table.find_custom_opt g with
               | Some txt ->
                 String.length txt > 4 && String.sub txt 0 4 = "%a0."
               | None -> false )
          in
          let rec reads depth e =
            match e with
            | MLapp (MLglob (g, _), MLrel k :: _)
              when k = depth + 1 && member_access g ->
              true
            | MLlam (_, _, b) -> reads (depth + 1) b
            | MLletin (_, _, x, b) -> reads depth x || reads (depth + 1) b
            | MLcase (_, sc, pv) ->
              reads depth sc
              || Array.exists
                   (fun (ids, _, _, br) -> reads (depth + List.length ids) br)
                   pv
            | MLfix (_, ids, funs, _) ->
              Array.exists (reads (depth + Array.length ids)) funs
            | e ->
              let found = ref false in
              Mlutil.ast_iter (fun x -> if reads depth x then found := true) e;
              !found
          in
          (match body with
           | MLcase (_, MLrel 1, pv) -> is_custom_match pv
           | _ -> false)
          || reads 0 body
        in
        let cpp_arg_info =
          List.mapi
            (fun j (id, ty, owned) ->
              let bare_cpp_ty =
                cpp_of_ml env ty
              in
              let stored_cpp_ty =
                convert_ml_type_to_cpp_type env ~ns:(!tctx).method_self_ns
                  tvars ty
              in
              let body_subst =
                match (bare_cpp_ty, stored_cpp_ty) with
                | Tglob (g1, [], _), Tshared_ptr (Tglob (g2, [], _))
                  when globref_equal g1 g2 && Table.is_coinductive g2 ->
                  Some (id, CPPderef (CPPvar id))
                | _ -> None
              in
              let unused =
                match List.nth_opt emitted_binder_indices j with
                | Some i -> not (Mlutil.ast_occurs (i + 1) a)
                | None -> false
              in
              let param_cpp_ty =
                match body_subst with
                | Some _ -> Tref (Lvalue, Tconst stored_cpp_ty)
                (* A binder the body never reads is a parameter only for its
                   callers, and the slot's own spelling is the one they call it
                   at: [Id_<std::any, ...>] takes its object as a box, whatever
                   the binder's annotation recorded -- [MemE], the family the
                   object stands for. *)
                | None when unused && Option.has_some (slot_param_cpp_ty j) ->
                  Option.get (slot_param_cpp_ty j)
                (* The binder's annotation is a definition unfolded -- [FusedS]
                   as [state * nat] -- and a class field in it names no
                   instance in this scope, so it would fall back to the
                   file-scope [std::any].  The slot writes the definition by
                   name, which its own declaration resolved. *)
                | None
                  when mentions_unresolved_promoted bare_cpp_ty
                       && Option.has_some (slot_param_cpp_ty j) ->
                  wrap_param_by_ownership ~is_owned:owned
                    (Option.get (slot_param_cpp_ty j))
                | None
                  when rank2_carrier <> None
                       && has_tany_in_type bare_cpp_ty
                       && not (Rank2.is_bare_box bare_cpp_ty) ->
                  Tref (Lvalue, Tconst (at_carrier bare_cpp_ty))
                | None
                  when prints_as_any bare_cpp_ty
                       && ( match slot_param_cpp_ty j with
                          | Some d -> not (prints_as_any d)
                          | None -> false ) ->
                  (* The binder's own annotation says nothing -- a constructor
                     eta-expanded into a lambda ([fmap inr m]) is handed a
                     parameter extraction never gave a type -- but the slot it
                     flows into does: the callee's instantiated domain.  Taking
                     the type from there is what keeps the signature and the
                     body in step, since the body was generated against the
                     concrete type the constructor needs.  Written [std::any]
                     instead, the parameter is a claim the body cannot keep,
                     and the error lands inside the lambda at the use. *)
                  wrap_param_by_ownership ~is_owned:owned
                    (Option.get (slot_param_cpp_ty j))
                | None
                  when Ml_type_util.has_tany_written bare_cpp_ty
                       && n_all_params = 1
                       && body_reads_members_of_binder a ->
                  (* A pattern lambda: the body decomposes this parameter with
                     a structured binding, which is ill-formed at [std::any].
                     Or it reads one of its members through a projection that
                     is spelled as member access ([fst si] as [si.first]),
                     which is ill-formed there just the same.
                     [crane_erase_fn] probes a generic callable with exactly
                     that -- and the binding is in the body, not the signature,
                     so no [requires] can absorb the failure and the probe
                     becomes a hard error.  Spelling the type keeps the probe
                     well-formed: CTAD then deduces a signature, and the
                     adapter unboxes at this very type, which is the one the
                     producer boxed.

                     Which type to spell is the slot's answer where it has
                     one.  The binder's own is assembled from an ML type whose
                     erased components were never inferred, so it erases a
                     whole component the container keeps
                     ([pair<Nat, std::any>] against a list of
                     [pair<Nat, Exp0<std::any>>]); the slot spells the
                     container's shape and leaves only the genuinely erased
                     leaf to [std::any].

                     It may refine the spelling only as far as still-erased,
                     though.  The body was generated against the erased view
                     and unboxes at it; a signature that erases nowhere is one
                     the body's casts no longer agree with. *)
                  let refined =
                    match slot_dom_cpp_ty j with
                    | Some slot ->
                      Ml_type_util.refine_param_from_slot ~tvars ~slot
                        bare_cpp_ty
                    | None -> bare_cpp_ty
                  in
                  wrap_param_by_ownership ~is_owned:owned refined
                | None
                  when (!tctx).itree_mode = Reified && ml_type_is_unit ty ->
                  (* A reified tree's continuation is typed [unit -> itree ...]
                     in ML, but [unit] is not one C++ type here: the value a
                     reified tree carries is whatever its consumer chose, and
                     the same Rocq type reaches the printer as [std::monostate]
                     over a concrete tree and as [std::any] over one whose
                     event type was erased.  The binder is under-determined
                     rather than erased -- nothing in the term says which -- so
                     it deduces.  Committing to [std::monostate] rejects every
                     call through an erased tree.  The slot is still emitted;
                     see the parameter filter above. *)
                  Tref (Lvalue, Tconst Tauto)
                | None when Ml_type_util.has_tany_written bare_cpp_ty ->
                  (* The type is spelled with erased positions (std::any).  Use
                     [const auto&] so the C++ compiler deduces the concrete
                     type at the call site — explicit std::any in the param
                     type would block valid calls and prevent field accesses
                     inside the body from resolving to the concrete type.

                     The erasure has to be one the spelling shows.  A type
                     whose erased argument sits in a position its template
                     never writes renders concretely, and a generic parameter
                     there is a liability: a consumer that probes the callable
                     with a [std::any] -- [crane_erase_fn] does -- instantiates
                     the body at [std::any] and fails inside it, where no
                     [requires] can catch it. *)
                  Tref (Lvalue, Tconst Tauto)
                | None -> wrap_param_by_ownership ~is_owned:owned bare_cpp_ty
              in
              (param_cpp_ty, Some id, body_subst) )
            filtered_args_with_owned
        in
        (* A binder the body never uses is a parameter with no name: named,
           it would be unused -- a [trigger Inc ;; k] continuation's [unit] --
           and could shadow a name the body introduces.  One kept only for the
           slot ({!binder_emitted}) is the common case. *)
        let arity_only =
          List.filteri
            (fun i _ -> not (Mlutil.ast_occurs (i + 1) a))
            args_with_owned
          |> List.map (fun (id, _, _) -> id)
        in
        let cpp_args =
          List.map2
            (fun (ty, id, _) (orig, _, _) ->
              (ty, if List.exists (( == ) orig) arity_only then None else id) )
            cpp_arg_info filtered_args_with_owned
        in
        (* A template parameter C++ cannot deduce is worse than the erasure
           it replaces, so the function object is polymorphic only where the
           carrier reaches a parameter: an erased position the body alone
           mentions stays [std::any].  {!mk_lambda} is what enforces that;
           asking it here keeps the body's generation in step with the
           signature it will be given. *)
        let carrier =
          match rank2_carrier with
          | Some x when deduces_tparam x (List.map fst cpp_args) -> Some x
          | _ -> None
        in
        (* The parameters' declared C++ types are only known here, after
           [cpp_arg_info]; correct the assignment made when their scope was
           opened above so the body reads what the signature says.  A
           parameter dropped by [filtered_args_with_owned] keeps its
           conversion-derived assignment. *)
        let () =
          let declared =
            List.combine
              (List.mapi (fun j (id, ml_ty, _) -> (j, (id, ml_ty)))
                 filtered_args_with_owned )
              cpp_arg_info
            |> List.map (fun ((j, (id, ml_ty)), (ty, _, _)) ->
                 (* A binder erasure would have removed, kept because the slot
                    takes it ({!binder_emitted}), holds whatever box the caller
                    passes. *)
                 if isTdummy ml_ty then (id, Tany)
                 else
                 (* A parameter the slot declares erased arrives as a box, even
                    though it is declared [const auto&] so the deduction can
                    also land on a concrete type.  Assign it [std::any] so uses
                    inside the body recover their own type from it; the
                    [Tauto] the declaration strips to would say, wrongly, that
                    the value is already what the body wants. *)
                 let assigned =
                   match (ty, expected_param_cpp_tys) with
                   | Tref (Lvalue, Tconst Tauto), Some doms
                     when ( match List.nth_opt doms (slot_dom j) with
                          | Some d -> prints_as_any d
                          | None -> false ) ->
                     Tany
                   | _ -> ty
                 in
                 (id, assigned))
          in
          assign_binder_types env
            ~cpp:(List.map (fun (id, _) -> List.assoc_opt id declared) args)
            args
        in
        let body_expected_ml_ty =
          let rec strip_arrows n ty =
            if n = 0 then Some ty
            else match resolve_tmeta ty with
                 | Miniml.Tarr (_, cod) -> strip_arrows (n - 1) cod
                 | _ -> None
          in
          (match slot.expected_ml_ty with
          | Some fn_ty ->
            (match strip_arrows n_all_params fn_ty with
            | Some cod ->
              (match resolve_tmeta cod with
              | Miniml.Tdummy _ | Miniml.Tunknown
              | Miniml.Tmeta {contents = None} -> slot.expected_ml_ty
              | _ -> Some cod)
            | None -> slot.expected_ml_ty)
          | None -> None)
        in
        (* Generate the body, then check if the body returns a lambda (this
           happens when extract_cons_app generates curried partial constructor
           applications with an MLmagic (_, barrier)). If so, convert the returned
           lambda to capture by value to avoid dangling references to the outer
           lambda's parameters. *)
        (* A lambda stored into an erased slot IS the value in that slot, so
           what it returns is erased too and its body inherits [deep_erase]. *)
        (* A [return] inside this lambda returns from the lambda, not from the
           enclosing function, so the body must not inherit the enclosing
           function's return type.  The slot this lambda flows into is the only
           thing that can say what the body returns.
           When the slot declares no signature at all -- a deduced [F0 &&]
           callback parameter, say -- there is nothing better to say, so the
           context is left alone.  A [void] codomain says nothing either: a
           unit-returning lambda spells its result [std::monostate] or nothing
           at all depending on what consumes it, which is a decision for the
           body's own generation. *)
        let with_lam_return_type f =
          match Option.map (unfold_cpp_typedef env) expected_ty with
          | _ when carrier <> None ->
            (* A polymorphic function object returns at the type its own
               parameter fixes, so the enclosing function's return type is
               not merely unhelpful here -- it is the wrong answer, and the
               body would spell it in place of the carrier.  What the body
               does return is the lambda's own ML codomain read at the
               carrier: the rank-2 variable is erased in that type, and the
               carrier is the name the parameter gave it back. *)
            let ret =
              match body_expected_ml_ty with
              | Some ml_ty ->
                Some
                  (at_carrier
                     (convert_ml_type_to_cpp_type env (get_current_type_vars ())
                        ml_ty))
              | None -> None
            in
            with_cpp_return_type ret f
          | Some (Tfun (_, cod)) when cod <> Tvoid ->
            (* Read in this scope: a variable of the callee's the slot names
               ([tfmap]'s [T2]) is erased where it sits, as the binders'
               types are, so what the body builds is what the slot reads. *)
            let scope = current_scope_type_names () in
            let cod =
              if not binders_left_open then cod
              else
              map_cpp_type
                (function
                  | Tvar tv as t ->
                    let id = tvar_spelled tv in
                    if List.exists (Id.equal id) scope then t else Tany
                  | t -> t )
                cod
            in
            with_cpp_return_type (Some cod) f
          | _ -> f ()
        in
        let body_stmts =
          (match carrier with
           | None -> (fun f -> f ())
           | Some _ -> with_rank2_carrier carrier)
            (fun () ->
              with_lam_return_type (fun () ->
                gen_stmts
                  ~slot:{slot with expected_ml_ty = body_expected_ml_ty}
                  env
                  (fun x -> Sreturn (Some x))
                  a ) )
        in
        let body_stmts =
          List.fold_left
            (fun stmts (_, _, subst) ->
              match subst with
              | Some (id, expr) -> List.map (local_var_subst_stmt id expr) stmts
              | None -> stmts )
            body_stmts
            cpp_arg_info
        in
        let body_stmts = return_captures_by_value body_stmts in
        (* When the lambda body is a standalone fixpoint (MLfix with no
           applied args), the fix represents a function value that would make
           this lambda curried — e.g. [fun x => fix f r := ...] generates
           [[=](x){auto f=...; return f;}] (1-arg returning fn) instead of
           the flat [[=](x,r){auto f=...; return f(r);}] (2-arg).  Fold the
           fix's own params into this lambda so the result is uncurried and
           directly compatible with [std::function<R(A,B)>] contexts. *)
        let cpp_args, body_stmts =
          match a with
          | MLfix (fix_x, _fix_ids, fix_funs, _)
            when List.length filtered_args <= 1 ->
            let fix_lam_params, _ = Mlutil.collect_lams fix_funs.(fix_x) in
            let fix_value_params =
              List.filter
                (fun (_, ty) -> not (isTdummy ty) && not (ml_type_is_void ty))
                fix_lam_params
            in
            ( match fix_value_params with
            | [] -> (cpp_args, body_stmts)
            | _ ->
              (* Only fold when body_stmts ends with a bare variable return,
                 i.e. the non-lifted ycomb path.  Lifted (polymorphic) fixes
                 are returned via a call expression and don't need folding. *)
              let last_is_var_return =
                match List.rev body_stmts with
                | Sreturn (Some (CPPvar _)) :: _ -> true
                | _ -> false
              in
              if not last_is_var_return then (cpp_args, body_stmts)
              else
                let extra_cpp_params =
                  List.mapi
                    (fun i (_, ml_ty) ->
                      let bare =
                        cpp_of_ml env ml_ty
                      in
                      let param_ty =
                        match bare with
                        | Tshared_ptr _ ->
                          Tref (Lvalue, Tconst bare)
                        | _ -> bare
                      in
                      (param_ty,
                       Some (Id.of_string (Printf.sprintf "_fea%d" i))) )
                    fix_value_params
                in
                let extra_args =
                  List.map
                    (fun (_, id_opt) -> CPPvar (Option.get id_opt))
                    extra_cpp_params
                in
                let rec modify_last_return = function
                  | [] -> []
                  | [Sreturn (Some e)] ->
                    [Sreturn (Some (mk_call e extra_args))]
                  | stmt :: rest -> stmt :: modify_last_return rest
                in
                (* The printer does List.rev on params, so put extra params
                   first (they will print last, after the outer lambda's own
                   params).  Within extra_cpp_params, reverse so that fix param
                   i prints at position i from the left (natural order). *)
                ( List.rev extra_cpp_params @ cpp_args,
                  modify_last_return body_stmts ) )
          | _ -> (cpp_args, body_stmts)
        in
        (* The return type annotation is left as [None]; loopify's
           [infer_saved_type] infers it from the body when computing frame
           struct field types.  Annotating here caused regressions for inner
           lambdas whose bodies return further closures (the inferred type
           became [std::function<...>] instead of the plain return type). *)
        let body_stmts =
          match carrier with
          | None -> body_stmts
          | Some _ ->
            let rec st s = map_stmt ex st at_carrier s
            and ex e = map_expr ex st at_carrier e in
            List.map st body_stmts
        in
        (* ... except where the body does nothing but throw: a deduced return
           type is [void] there, and no slot that asked for a value can take
           it.  The slot's own codomain is what the throw stands in for, so
           name that. *)
        (* ... and where the body is a match whose branches produce
           different instantiations -- a dependent match refines the lambda's
           erased type binder per branch ([Ret (inl 0)] at the index, [inr <$>
           ...] at [nat + nat]) -- a deduced return type is rejected.  The
           lambda's own result erases what the branches disagree on, and each
           converts to it. *)
        let rec join a b =
          if a = b then a
          else
            match (a, b) with
            | Tglob (g, xs, es), Tglob (g', ys, _)
              when GlobRef.CanOrd.equal g g' && List.length xs = List.length ys ->
              Tglob (g, List.map2 join xs ys, es)
            | Tnamespace (ns, x), Tnamespace (_, y) -> Tnamespace (ns, join x y)
            | _ -> Tany
        in
        let rec leaf_rtys = function
          | MLcase (_, _, pv) ->
            List.concat_map
              (fun (_, rty, _, body) ->
                match body with
                | MLcase _ | MLletin _ -> leaf_rtys body
                | _ -> [rty] )
              (Array.to_list pv)
          | MLletin (_, _, _, b) -> leaf_rtys b
          | _ -> []
        in
        let dropped_type_binder =
          List.exists (fun (_, ty, _) -> isTdummy ty) args_with_owned
        in
        let branch_join =
          if not dropped_type_binder then None
          else
            match List.map (cpp_of_ml env) (leaf_rtys a) with
            | t :: (_ :: _ as rest) ->
              let j = List.fold_left join t rest in
              if prints_as_any j || not (names_only_scoped_tvars j) then None
              else Some j
            | _ -> None
        in
        (* Branches refined by an enclosing function's type binder may
           disagree just the same -- [memM_interp]'s [Load] branch builds at
           [nat], the other at the index [T2] -- and the annotations do not
           show it, being the case's.  With more than one leaf, the slot,
           where it states a result this scope can write, is what each
           converts to. *)
        let slot_result_on_disagreement () =
          match leaf_rtys a with
          | _ :: _ :: _ -> (
            match Option.map strip_cpp_ref_const expected_ty with
            | Some (Tfun (_, cod))
              when cod <> Tvoid && (not (prints_as_any cod))
                   && names_only_scoped_tvars cod ->
              Some cod
            | _ -> None )
          | _ -> None
        in
        let ret_ann =
          match body_stmts with
          | [Sthrow _] | [Sreturn (Some (CPPabort _))] -> (
            match Option.map strip_cpp_ref_const expected_ty with
            | Some (Tfun (_, cod)) when cod <> Tvoid -> Some cod
            | _ -> None )
          | _ -> (
            match branch_join with
            | Some _ as j -> j
            | None -> slot_result_on_disagreement () )
        in
        mk_lambda
          ?tparams:(Option.map (fun x -> [x]) carrier)
          (List.rev cpp_args) ret_ann body_stmts ~capture:Closure )
    in
    restore_env_types saved_env_types;
    ( match filtered_args with
    | [] ->
      (* All lambda params are dummy (type abstractions). Skip the lambda
         wrapper and generate the body expression directly. However, when the
         body is a reference to a template function (detectable by having
         Tdummy-typed leading params in its ML type), we must wrap it in a
         generic forwarding lambda — C++ cannot pass overloaded or template
         function names as first-class values. *)
      ( match a with
      | MLglob (r, tys_inner) ->
        let ml_ty =
          match find_type_opt r with
          | Some ty -> ty
          | None -> Tunknown
        in
        let has_dummy_prefix = function
          | Tarr (t, _) when isTdummy t -> true
          | _ -> false
        in
        if has_dummy_prefix ml_ty then
          (* The function is a template that had type-level leading params. We
             need a forwarding lambda because C++ can't pass template function
             names as first-class values.

             To handle non-deducible template type params (like T2 that only
             appears in the return type), we use a C++20 template lambda with
             explicitly typed value parameters. This lets the compiler deduce
             type variables from the argument types, and we compute
             non-deducible tvars via std::invoke_result_t. *)
          let rec collect_non_dummy_types = function
            | Miniml.Tarr (t, rest) when not (isTdummy t) ->
              t :: collect_non_dummy_types rest
            | Miniml.Tarr (_, rest) -> collect_non_dummy_types rest
            | _ -> []
          in
          let non_dummy_param_tys = collect_non_dummy_types ml_ty in
          let n = List.length non_dummy_param_tys in
          let is_unary_method = n = 1 && is_methodified r in
          if is_unary_method then
            (* The function was methodified: it is spelled [x.f()], not [f(x)],
               so no forwarding lambda can name it.  Emit the plain reference
               and let the printer wrap it in the method-calling lambda it
               already builds for method values. *)
            gen_expr env a
          else
          let arg_ids = List.init n field_param_id in
          let arg_vars = List.map (fun id -> CPPvar id) arg_ids in
          (* Collect all tvars from the ML type *)
          let all_tvars_set =
            List.fold_left
              collect_tvars_set
              IntSet.empty
              (non_dummy_param_tys @ [ml_ty])
          in
          let all_tvars = IntSet.elements all_tvars_set in
          (* Tvars deducible from non-function value params *)
          let value_param_tys =
            List.filter
              (fun t ->
                match t with
                | Miniml.Tarr _ -> false
                | _ -> true )
              non_dummy_param_tys
          in
          let deducible_set =
            List.fold_left
              (fun acc t -> spelled_tvars_of acc t)
              IntSet.empty value_param_tys
          in
          let deducible_tvars = IntSet.elements deducible_set in
          let non_deducible_tvars =
            List.filter (fun i -> not (IntSet.mem i deducible_set)) all_tvars
          in
          (* The lambda's own type binders, named so the callee's variables
             do not read as the enclosing declaration's. *)
          let local_tvar i = Generated_name.indexed "T" i in
          let local_tvars =
            List.init (List.fold_left max 0 all_tvars) (fun k -> local_tvar (k + 1))
          in
          let local_ty ty = template_arg_of_ml_type env local_tvars ty in
          (* A forwarding parameter, and the argument that forwards it. *)
          let forwarding = Tref (Forwarding, Tauto) in
          let forward x = CPPforward (Texpr_type x, x) in
          (* What the callee returns once given its value arguments, in the
             lambda's own variables. *)
          let result_ml = Ml_type_util.ml_drop_arrows n ml_ty in
          (* The lambda returns what the call does: its type where every
             variable in it is named, [decltype(auto)] -- the call's own
             answer -- where one is not. *)
          let lambda ?ret tparams params call =
            let ret =
              match ret with
              | Some t
                when (not (Ml_type_util.has_unnamed_tvar t)) && not (prints_as_any t)
                ->
                t
              | _ -> Tdecltype_auto
            in
            mk_lambda ~tparams
              (List.map2 (fun ty id -> (ty, Some id)) params arg_ids)
              (Some ret) [Sreturn (Some call)] ~capture:Closure
          in
          if non_deducible_tvars <> [] && not (IntSet.is_empty deducible_set)
          then
            (* A template lambda with typed value parameters, which deduce the
               variables they spell; the function-typed parameter is
               forwarding, and a variable only the result names is the type
               that parameter returns at the deduced ones. *)
            let params =
              List.map
                (function
                  | Miniml.Tarr _ -> forwarding
                  | ty -> Tref (Lvalue, Tconst (local_ty ty)) )
                non_dummy_param_tys
            in
            let fwd_args =
              List.map2
                (fun x ty ->
                  match ty with Miniml.Tarr _ -> forward x | _ -> x )
                arg_vars non_dummy_param_tys
            in
            let invoke_result =
              Tid_external
                ( "std::invoke_result_t",
                  Tref (Lvalue, Texpr_type (List.hd arg_vars))
                  :: List.map (fun j -> Tref (Lvalue, Tvar (Tv_index (j, Some (local_tvar j)))))
                       deducible_tvars )
            in
            let ty_args =
              List.map
                (fun i ->
                  if IntSet.mem i deducible_set then Tvar (Tv_index (i, Some (local_tvar i)))
                  else invoke_result )
                (List.sort compare (deducible_tvars @ non_deducible_tvars))
            in
            let ret =
              Minicpp.subst_cpp_tvars
                (fun i ->
                  if IntSet.mem i deducible_set then
                    Some (Tvar (Tv_index (i, Some (local_tvar i))))
                  else Some invoke_result )
                (local_ty result_ml)
            in
            lambda ~ret
              (List.map local_tvar deducible_tvars)
              params
              (mk_call (mk_cppglob r ty_args) fwd_args)
          else
            (* Simple forwarding.  A parameter whose type names no variable is
               written at it: a value stored behind [std::any] is then unboxed
               by [crane_erase_fn] at that type rather than handed on boxed.
               With no type argument given, the variables are this lambda's
               own type binders, which nothing outside instantiates: the
               consumer, erased too, hands the value over at [std::any] --
               [interp] calling a named handler [h] with an event.  Every
               variable is then written as the box it is, and a parameter
               that mentions one is read at that erased type. *)
            let own_index = tys_inner = [] && all_tvars <> [] in
            let at_own_index ty =
              Ml_type_util.resolve_tvars_to_any
                (convert_ml_type_to_cpp_type env [] ty)
            in
            let mentions_tvar ty =
              not (IntSet.is_empty (collect_tvars_set IntSet.empty ty))
            in
            let params =
              List.map
                (fun ty ->
                  match ty with
                  | Miniml.Tarr _ -> forwarding
                  | _ when IntSet.is_empty (spelled_tvars_of IntSet.empty ty) ->
                    Tref (Lvalue, Tconst (convert_ml_type_to_cpp_type env [] ty))
                  | _ when own_index -> Tref (Lvalue, Tconst Tauto)
                  | _ -> forwarding )
                non_dummy_param_tys
            in
            let fwd_args =
              List.map2
                (fun x ty ->
                  match ty with
                  | Miniml.Tarr _ -> forward x
                  | _ when own_index && mentions_tvar ty ->
                    CPPconvert (at_own_index ty, x)
                  | _ -> forward x )
                arg_vars non_dummy_param_tys
            in
            (* Convert inner type args to C++ types, filtering out Tany *)
            let inner_tvars = get_current_type_vars () in
            let tys_cpp =
              List.map
                (convert_ml_type_to_cpp_type env inner_tvars)
                tys_inner
            in
            (* An erased argument is left to deduction -- unless nothing can
               deduce it: [h : getE ~> itree noE] quantifies an index the
               enum [getE] does not carry, and the consumer, which erased it
               too, takes the tree at [std::any].  With no argument given at
               all -- the index is this lambda's own type binder -- every
               variable is such a one, since none is deducible here. *)
            let tys_cpp =
              if own_index then
                List.init (List.fold_left max 0 all_tvars) (fun _ -> Tany)
              else if non_deducible_tvars = [] then List.filter (fun t -> t <> Tany) tys_cpp
              else if tys_cpp = [] then List.map (fun _ -> Tany) non_deducible_tvars
              else tys_cpp
            in
            let ret =
              Minicpp.subst_cpp_tvars
                (fun i -> List.nth_opt tys_cpp (i - 1))
                (convert_ml_type_to_cpp_type env [] result_ml)
            in
            lambda ~ret [] params (mk_call (mk_cppglob r tys_cpp) fwd_args)
        else
          (* Every binder was a type: the body is the value the slot takes. *)
          gen_expr ?expected_ty ~slot env a
      | _ ->
        (* Body is not a template function ref — wrap in void thunk (old
           behavior). gen_expr env a might produce lambdas with [&] capture
           which fail at static scope, so we use the pre-built capture-free
           lambda f.

           Exception: in reified mode, when the lambda had void-typed params
           (from monadic result type erasure), keep the lambda as a function
           object rather than an IIFE. This is needed for itree_bind
           continuations which expect std::function, not the result of
           calling the function. *)
        if (!tctx).itree_mode = Reified
           && List.exists (fun (_, ty) -> ml_type_is_unit_or_void ty) lam_params then
          f
        else
          mk_call f [] )
    | _ ->
      let ml_arity =
        match slot.expected_ml_ty with
        | Some ty -> count_ml_value_arrows ty
        | None -> 0
      in
      (* Whether any branch of the lambda's own body returns a closure.  Only
         the statement structure is walked: a lambda nested inside some other
         expression is not this lambda's result. *)
      let returns_a_lambda =
        match f with
        | CPPlambda {cl_body = body; _} ->
          let found = ref false in
          let rec walk s =
            ( match s with
            | Sreturn (Some (CPPlambda _)) -> found := true
            | _ -> () );
            ignore (map_stmt Fun.id (fun s -> walk s; s) Fun.id s)
          in
          List.iter walk body;
          !found
        | _ -> false
      in
      eta_expand_to_expected ?expected_ty ~ml_arity ~returns_a_lambda
        ~arity:(List.length filtered_args) f )
  | MLglob (x, tys) when is_inline_custom x ->
    let ml_ty = find_type x in
    let ty = cpp_of_ml env ml_ty in
    ( match ty with
    | Tfun (dom, cod) ->
      eta_fun ?expected_ty env (MLglob (x, tys)) []
    | _ ->
      mk_cppglob ?yields:(glob_yields env x tys)
        x (template_params_of_ml env tys) )
  | MLglob (x, tys) ->
    let tvars = get_current_type_vars () in
    let tys_cpp =
      List.map
        (fun ty ->
          let t =
            cpp_of_ml env (type_simpl ty)
          in
          match t with
          | Tvar (Tv_index (_, None)) when tvars <> [] ->
            Terased Ek_type
          | _ -> t )
        tys
    in
    let tys_cpp = hkt_spelled_type_args x tys_cpp in
    (* A global passed as a function value -- [MonadIter_itree] at a slot
       [MonadIter m] -- has its erased type arguments stated by the callable
       the slot takes. *)
    let tys_cpp =
      match (List.exists prints_as_any tys_cpp, slot.call_result) with
      | true, (Some _ as res) -> (
        match instance_family_binding env x tys res with
        | Some (_, names, m) ->
          List.mapi
            (fun k t ->
              if not (prints_as_any t) then t
              else
                match List.nth_opt names k with
                | Some v -> (
                  match List.find_opt (fun (v', _) -> Id.equal v v') m with
                  | Some (_, b) when names_only_scoped_tvars b -> b
                  | _ -> t )
                | None -> t )
            tys_cpp
        | None -> tys_cpp )
      | _ -> tys_cpp
    in
    let tys_cpp =
      match expected_ty with
      | Some _ when tys_cpp = [] -> (
        (* None written at all: every variable, if the callable binds each. *)
        match callee_result_bindings env x ~explicit:true expected_ty with
        | (_ :: _ as names), (_ :: _ as m) -> (
          let bound =
            List.map
              (fun v ->
                match List.find_opt (fun (v', _) -> Id.equal v v') m with
                | Some (_, b) when names_only_scoped_tvars b -> Some b
                | _ -> None )
              names
          in
          if List.for_all (fun b -> b <> None) bound then
            List.map Option.get bound
          else tys_cpp )
        | _ -> tys_cpp )
      | Some _ when List.exists prints_as_any tys_cpp -> (
        match callee_result_bindings env x ~explicit:true expected_ty with
        | names, (_ :: _ as m) ->
          List.mapi
            (fun k t ->
              if not (prints_as_any t) then t
              else
                match List.nth_opt names k with
                | Some v -> (
                  match List.find_opt (fun (v', _) -> Id.equal v v') m with
                  | Some (_, b) when names_only_scoped_tvars b -> b
                  | _ -> t )
                | None -> t )
            tys_cpp
        | _ -> tys_cpp )
      | _ -> tys_cpp
    in
    let yields = glob_yields env x tys in
    let cglob =
      match filter_erased_type_args tys_cpp with
      | [] -> mk_cppglob ?yields x (phantom_prefix_args x)
      | tys_cpp -> mk_cppglob ?yields x tys_cpp
    in
    let needs_call =
      match find_type_opt x with
      | Some ml_ty when is_monadic_ml_type ml_ty -> true
      | Some _ when Table.is_cofixpoint x -> true
      (* A definition that only throws is emitted as a zero-parameter function
         unless it has C++ parameters of its own, in which case naming it is
         naming a function. *)
      | Some ml_ty when Table.is_throwing_value x ->
        ( match cpp_of_ml env ml_ty with
        | Tfun _ -> false
        | _ -> true )
      | _ -> false
    in
    if needs_call then
      mk_call cglob []
    else
      ( match
          Option.map
            (fun ty ->
              materialise_opaque (cpp_of_ml env (expand_ml_fun_alias ty)))
            (find_type_opt x)
        with
      (* A declaration whose result erased -- because its Rocq type hides
         the quantifier behind a type alias, or because a type index alone
         pins the result down -- hands back a box whatever the use site's
         instantiation says, so a use site naming concrete types reaches it
         through the adapter {!coerce} builds.  The type the use site wants
         is the slot's when there is one; failing that, a single type
         argument tells what the one quantifier every erased position came
         from was instantiated at. *)
      | Some from
        when (match from with Tfun (_, cod) -> prints_as_any cod | _ -> false)
        ->
        let into =
          match (expected_ty, tys_cpp) with
          | Some into, _ when names_only_scoped_tvars into -> Some into
          | _, [t] when not (prints_as_any t) ->
            let rec instantiate = function
              | Tany -> t
              | Tfun (dom, cod) ->
                Tfun (List.map instantiate dom, instantiate cod)
              | ty -> ty
            in
            Some (instantiate from)
          | _, _ -> None
        in
        (* A signature that erased entirely is not a template and takes no
           explicit type arguments; one that kept some is still called with
           the ones the use site supplied. *)
        let cglob =
          if is_fully_erased_fun_ty from then mk_cppglob x [] else cglob
        in
        ( match into with
        | Some into -> coerce ~from ~into cglob
        | None -> cglob )
      | _ -> curry_to_expected env ?expected_ty ~tys x cglob )
  | MLcons (_ty, r, _ts)
    when match r with
         | GlobRef.ConstructRef ((kn, i), _) ->
           Table.is_numeral_inductive (GlobRef.IndRef (kn, i))
         | _ -> false ->
    (* Try to fold Peano numeral chain into an integer literal *)
    let ind_ref =
      match r with
      | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
      | _ -> CErrors.anomaly (Pp.str "try_fold_numeral: expected ConstructRef")
    in
    ( match Table.get_numeral_info ind_ref with
    | Some info ->
      ( match try_fold_numeral info ml_e with
      | Some n ->
        render_numeral info (Z.of_int n)
      | None ->
        (* Peano folding failed.  Try binary positive folding for
           Z constructors: Zpos(xI(xO(...xH...))) / Zneg(...) chains
           can overflow unsigned int, so fold into INT64_C(n) literals. *)
        let z_folded =
          match (_ts, r) with
          | [inner], GlobRef.ConstructRef (_, cidx) ->
            try_fold_z_binary info cidx inner
          | _ -> None
        in
        ( match z_folded with
        | Some e -> e
        | None -> gen_expr_custom_cons ?expected_ty ~slot env _ty r _ts ) )
    | None -> gen_expr_custom_cons ?expected_ty ~slot env _ty r _ts )
  | MLcons (ty, r, ts) when is_custom r ->
    gen_expr_custom_cons ?expected_ty ~slot env ty r ts
  | MLcons (ty, r, ts)
    when ts = []
         &&
         match r with
         | GlobRef.ConstructRef ((kn, _), _) ->
           is_enum_inductive (GlobRef.IndRef (kn, 0))
         | _ -> false ->
    let ind_ref, ctor_name =
      match r with
      | GlobRef.ConstructRef ((kn, i), cidx) ->
        ( GlobRef.IndRef (kn, i),
          Id.of_string (Common.enum_ctor_name_of_ref kn i cidx) )
      | _ ->
        CErrors.anomaly
          (Pp.str "gen_expr: enum constructor expected ConstructRef")
    in
    CPPenum_val (ind_ref, ctor_name)
  | MLcons (ty, r, ts) ->
    (* A value built directly into an erased ([std::any]) slot -- the
       enclosing function's C++ return type is opaque, as for a definition
       whose return type is value-dependent -- must use the canonical erased
       shape: a consumer of such a slot recovers it with a fixed [any_cast]
       and cannot know the concrete type arguments.  That is the same
       requirement [deep_erase] expresses for a value flowing into an
       erased field or parameter. *)
    let slot =
      { slot with
        deep_erase =
          slot.deep_erase
          ||
          ( match (!tctx).current_cpp_return_type with
          | Some t -> resolves_to_any_type t
          | None -> false ) }
    in
    (* The annotation carries this producer's own instantiation, and a stored
       closure whose arrows extraction never unified leaves it erased -- a
       [rose (option (nat -> nat))] node is annotated at
       [rose<optional<function<any(any)>>>] while the consumer names the
       concrete one.  Where the position states the same inductive, its
       arguments are the ones both sides agree on, so take them for the
       positions the annotation erased.  Not under [deep_erase]: there the
       erased instantiation {i is} the canonical one. *)
    let ty =
      match (resolve_tmeta ty, Option.map resolve_tmeta slot.expected_ml_ty) with
      | Miniml.Tglob (n, tys, sc), Some (Miniml.Tglob (n', exp_tys, _))
        when (not slot.deep_erase)
             && globref_equal n n'
             && List.length tys = List.length exp_tys
             && List.exists (ml_type_contains_erased ~in_arrows:true) tys ->
        Miniml.Tglob
          ( n,
            List.map2
              (fun local outer ->
                if ml_type_contains_erased ~in_arrows:true local then outer
                else local )
              tys exp_tys,
            sc )
      | _ -> ty
    in
    (* Setting [in_constructor_expr] makes unresolvable promoted vars (those
       NOT in [promoted_var_map]) fall back to [Tany] = [std::any].

       For non-record constructors (fds = []), we keep [promoted_var_map] so
       that template type annotations (e.g., SigT<..., Path<typename
       _tcI0::Obj>>) match the function's declared return type.

       For record constructors (fds != []), we clear [promoted_var_map]
       because record structs use erased types (std::any) for promoted fields,
       so lambda parameters assigned to record fields must also use std::any. *)
    with_in_constructor_expr true @@ fun () ->
    (* A record's arm narrows the map below; the scope puts it back. *)
    with_promoted_var_map (!tctx).promoted_var_map @@ fun () ->
    (* When an erased argument (a value-dependent leaf boxed as [std::any],
       holding a custom list whose elements are fully erased —
       [deque<std::any>] — at runtime) flows into a constructor/record field
       whose concrete type is a custom list with a NON-erased element type
       (e.g. [mkRec : list elt -> rec] → field [deque<elt>]), the [MLrel]/
       [MLmagic] arg path only unwraps it to the erased [deque<std::any>].
       Convert that to the concrete-element container with [crane_container_cast]
       here, where the field's concrete type is known — a plain aggregate
       initialization / [any_cast<deque<elt>>] would fail, since the value is a
       [deque<std::any>].  Shared by the value-type-variant factory path
       ([gen_and_wrap]) and the record/aggregate path.  Mirrors [eta_fun]'s
       function-argument container-cast path. *)
    let container_cast_erased_field ml_ft ml_arg expr =
      let is_erased_rel =
        match ml_arg with
        | MLrel j | MLmagic (_, MLrel j) ->
          binder_is_boxed j
        | _ -> false
      in
      if not is_erased_rel then expr
      else begin
        let ct = cpp_of_ml env ml_ft in
        let clean_ct = clean_self_ns ct in
        match strip_ns_tglob clean_ct with
        | Tglob (g, [elem_ty], _)
          when Ml_type_util.is_custom_list_global g
               && not (resolves_to_any_type elem_ty) ->
          (* [expr] came out as the erased [deque<std::any>] from the
             MLrel/MLmagic path; rebuild it as the concrete element container. *)
          CPPcontainer_cast (clean_ct, expr, false)
        | _ -> expr
      end
    in
    let fds = record_fields_of_type ty in
    let cons_result = match fds with
    | [] ->
      (* Propagate resolved types to nested list constructors before code
         generation. For List<nat> constructors like cons(1, cons(2, nil)), this
         ensures the nested nil gets List<nat> type instead of
         List<std::any>. *)
      let ts_updated =
        match ty with
        | Tglob (n, tys_orig, schema_opt) ->
          (* Only run type propagation for list constructors *)
          let is_list =
            try String.equal (Common.pp_global_name Type n) "list"
            with _ -> false
          in
          if not is_list then
            ts
          else (* Filter out index type args - only keep parameters *)
            let tys_filt =
              match n with
              | GlobRef.IndRef (kn, _) ->
                ( match Table.get_ind_num_param_vars_opt kn with
                | Some num_param_vars -> safe_firstn num_param_vars tys_orig
                | None -> tys_orig )
              | _ -> tys_orig
            in
            (* Resolve Tunresolved from element types *)
            let has_unknown =
              List.exists
                (fun (t : ml_type) ->
                  match t with
                  | Tunknown -> true
                  | _ -> false )
                tys_filt
            in
            if
              has_unknown
              &&
              match ts with
              | [] -> false
              | _ -> true
            then
              let tys_resolved =
                List.map
                  (fun (t : ml_type) ->
                    match t with
                    | Tunknown ->
                      let first_elem =
                        List.find_opt
                          (fun a ->
                            match a with
                            | MLdummy _ -> false
                            | _ -> true )
                          ts
                      in
                      ( match first_elem with
                      | Some (MLmagic (_, MLcons (elem_ty, _, _))) -> elem_ty
                      | Some (MLcons (elem_ty, _, _)) -> elem_ty
                      | _ -> t )
                    | _ -> t )
                  tys_filt
              in
              (* Propagate resolved type to nested constructors *)
              let resolved_ty = Miniml.Tglob (n, tys_resolved, schema_opt) in
              let rec update_nested_ty ast =
                match ast with
                | MLcons (arg_typ, arg_c, arg_ts) ->
                  ( match arg_typ with
                  | Miniml.Tglob (arg_ref, arg_tys, _)
                    when GlobRef.CanOrd.equal arg_ref n
                         && List.exists
                              (fun t ->
                                match t with
                                | Miniml.Tunknown -> true
                                | _ -> false )
                              arg_tys ->
                    MLcons (resolved_ty, arg_c, List.map update_nested_ty arg_ts)
                  | _ ->
                    MLcons (arg_typ, arg_c, List.map update_nested_ty arg_ts) )
                | MLmagic (m, inner) -> MLmagic (m, update_nested_ty inner)
                | other -> other
              in
              List.map update_nested_ty ts
            else
              ts
        | _ -> ts
      in
      (* Where the position already spells this inductive, it -- not the
         constructor's own type annotation -- says how the type arguments are
         written.  An element type that reached the slot through one of the
         callee's type variables keeps the currying the declaration wrote it
         at: once a function type has been substituted for a type variable,
         its arrows are indistinguishable from the callee's own, so converting
         the annotation cannot recover the shape. *)
      (* Refine, never respell.  The position says what an argument the
         annotation left erased is -- and equally what one it erased too
         deeply is, since two producers for one declared field must agree
         about which of its arguments are [std::any].  What it may not do is
         overrule a concrete argument with a different concrete one: inside a
         bind's action the expected type is the enclosing declaration's
         result, not the action's, and a constructor whose type parameter none
         of its arguments constrains would then be built at [EOU<Dv>] where
         the action is an [EOU<bool>].

         Currying is not a respelling: an element type that reached the slot
         through one of the callee's type variables keeps the arity the
         declaration wrote it at, which converting the annotation cannot know
         -- the arrows of a function substituted into a type variable are
         indistinguishable from the callee's own.  Two spellings that curry
         to the same type are therefore one type, and the position's is the
         one a template argument position requires.  So is an alias and what
         it expands to: the position names [List<entry<T1>>] where the
         annotation has the pair behind it, and the name is what the
         declaration wrote. *)
      let temps_from_slot ind temps =
        let erased_anywhere = exists_cpp_type prints_as_any in
        (* With no slot of its own, a constructor is the value the enclosing
           function returns, as Step 2b below reads it -- [go (RetF x)] in
           [trigger]'s continuation, whose family its annotation erased --
           and only an erased position is ever taken from it. *)
        let slot_ty =
          match expected_ty with
          | Some _ -> expected_ty
          | None -> (
            match (!tctx).current_cpp_return_type with
            | Some (Tshared_ptr t) -> Some t
            | t -> t )
        in
        match
          Option.map
            (fun t -> unfold_cpp_typedef env (Ml_type_util.unqualify_ty t))
            slot_ty
        with
        | Some (Tglob (ind', args, _))
          when globref_equal ind' ind && List.length args = List.length temps ->
          List.map2
            (fun local outer ->
              (* Compared after unfolding throughout, not only at the head:
                 the same type is written [entry<T1>] in one place and the
                 pair behind it in the other, and one of the two spellings
                 carries the namespace the declaration is read in. *)
              let rec expand t =
                let t' =
                  match unfold_cpp_typedef env t with
                  | Tnamespace (_, inner) -> inner
                  | t' -> t'
                in
                if t' = t then t else expand t'
              in
              let norm t = map_cpp_type expand t in
              let same_type a b =
                curry_fun_type (norm a) = curry_fun_type (norm b)
              in
              if
                erased_anywhere local || erased_anywhere outer
                || same_type local outer
              then outer
              else local )
            temps args
        | _ -> temps
      in
      (* In dependent types, if a constructor arg at position i is
         [MLdummy Ktype] (a type-valued argument — e.g. [x : A] where
         [A : Type]), any template param at a later position j > i must
         also be erased to [std::any].
         Rationale: later params often have types that are functions of
         the erased type variable (e.g. [P x] for [sigT A P]).  When A
         is erased, [P x] is equally abstract and the concrete type
         inferred from the value argument (e.g. [bool] from [true : bool])
         would produce an incompatible template instantiation
         ([SigT<std::any, Bool0>] vs. the declared
         [SigT<std::any, List<std::any>>]).  {!index_erase_type} is the
         same erasure the type side applies to those positions in
         {!convert_ml_type_to_cpp_type}, so the two agree by construction. *)
      let erase_past_type_arg temps =
        let rec first_ktype_dummy i = function
          | [] -> max_int
          | (MLdummy Ktype | MLmagic (_, MLdummy Ktype)) :: _ -> i
          | _ :: rest -> first_ktype_dummy (i + 1) rest
        in
        let cutoff = first_ktype_dummy 0 ts_updated in
        List.mapi (fun i t -> if i > cutoff then index_erase_type t else t) temps
      in
      (* Generate: Type<temps>::ctor::Constructor_(args) *)
      let gen_ctor_call args =
        match ty with
        | Tglob (n, tys, _) ->
          (* Filter out index type args - only keep parameters *)
          let tys =
            match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys
              | None -> tys )
            | _ -> tys
          in
          (* Resolve Tunresolved type args from constructor element types. For
             cons(elem, rest), elem's type provides the list's type param. *)
          let has_unknown =
            List.exists
              (fun (t : ml_type) ->
                match t with
                | Tunknown -> true
                | _ -> false )
              tys
          in
          let tys =
            if
              has_unknown
              &&
              match ts_updated with
              | [] -> false
              | _ -> true
            then
              List.map
                (fun (t : ml_type) ->
                  match t with
                  | Tunknown ->
                    (* Infer from first non-MLmagic/MLdummy constructor arg *)
                    let first_elem =
                      List.find_opt
                        (fun a ->
                          match a with
                          | MLdummy _ -> false
                          | _ -> true )
                        ts_updated
                    in
                    ( match first_elem with
                    | Some (MLmagic (_, MLcons (elem_ty, _, _))) -> elem_ty
                    | Some (MLcons (elem_ty, _, _)) -> elem_ty
                    | _ -> t )
                  | _ -> t )
                tys
            else
              tys
          in
          let temps = template_params_of_ml ~curry:false env tys in
          (* Where the position expects this very inductive, it -- not the
             constructor's own type annotation -- says how the arguments are
             spelled.  An element type that reached the slot through one of
             the callee's type variables keeps the currying the declaration
             wrote it at, which converting the annotation cannot know: the
             arrows of a function substituted into a type variable are
             indistinguishable from the callee's own. *)
          let temps = temps_from_slot n temps in
          (* Normalize out-of-range [Tvar(_, None)] type args to [std::any] when
             this constructor is nested as an argument of another constructor.
             Such a Tvar prints as a bogus, undeclared template parameter name
             (e.g. [List<T1>]) — it arises when a value with an erased/promoted
             type parameter (e.g. a record's [Type]-valued field used in a
             dependent [list <that field>] field) is built at a concrete
             instance.  The erased struct field is [std::any], so the value must
             be too.  Restricted to the nested-argument case so a top-level
             constructor call with a genuine (return-only) template parameter
             (e.g. [Trie<T1>::empty()] in a template method) is left intact. *)
          let temps =
            if slot.in_ctor_arg then List.map erase_unresolved_tvars temps
            else temps
          in
          (* For inductives with dependent parameters (e.g. sigT where the
             second param's type references the first), the dependent type arg
             extracts as a bare reference to the same inductive as an earlier
             arg.  Erase the duplicate to Tany to avoid mismatched template
             instantiations. *)
          let temps =
            if Table.has_dependent_params n then
              let expected_temps =
                expected_type_args_from_return env ?slot:expected_ty n
                  ~arity:(List.length temps)
              in
              match expected_temps with
              | Some exp_tys ->
                List.mapi (fun i t ->
                  let exp_t = normalize_erased_types (List.nth exp_tys i) in
                  if t <> exp_t && prints_as_any exp_t then Tany
                  else if t <> exp_t then exp_t
                  else t
                ) temps
              | None ->
                match tys with
                | [fst_ty; snd_ty] ->
                  let same_base = match fst_ty, snd_ty with
                    | Miniml.Tglob (g1, _, _), Miniml.Tglob (g2, sub2, _) ->
                      GlobRef.CanOrd.equal g1 g2 && sub2 = []
                    | _ -> false
                  in
                  if same_base then
                    match temps with
                    | [fst; _] -> [fst; Tany]
                    | _ -> temps
                  else temps
                | _ -> temps
            else temps
          in
          (* When all template params resolved to Tany (all type args were
             unresolved Tmeta), try to recover the concrete element type from
             an expected type threaded down from an enclosing constructor.
             Example: the pair (Fr [...], []) has a concrete pair annotation
             with second type arg list(parser_frame); when generating the nil
             for the second slot, [expected_ml_ty] = list(parser_frame),
             so we produce List<Parser_frame>::nil() instead of List<any>::nil(). *)
          let temps =
            (* Treat unnamed Tvars (Tvar(_, None)) as erased: they become
               std::any after tvar_erase_type, so we should try to recover
               the concrete type from the expected type annotation. *)
            let is_effectively_erased t =
              prints_as_any t || (match t with Tvar (Tv_index (_, None)) -> true | _ -> false)
            in
            if List.for_all is_effectively_erased temps && temps <> [] then
              (* Resolve any metas in the expected type before matching.
                 The let-binding type may be Tmeta{Some Tglob(...)} so we
                 need to unwrap the meta to get the concrete Tglob. *)
              let expected_resolved = Option.map resolve_tmeta slot.expected_ml_ty
              in
              (match expected_resolved with
              | Some (Miniml.Tglob (exp_n, exp_tys, _))
                when GlobRef.CanOrd.equal n exp_n
                     && List.length exp_tys = List.length tys ->
                (* Compute the recovered type with in_constructor_expr = false so
                   that promoted type vars resolve via promoted_var_map (giving
                   e.g. typename D::Defs::Parser_frame) rather than being erased
                   to std::any by the constructor-expression shortcut. *)
                let recovered =
                  with_in_constructor_expr false (fun () ->
                      template_params_of_ml ~curry:false env exp_tys )
                in
                if List.for_all (fun t -> not (prints_as_any t)) recovered
                then recovered
                else temps
              | _ -> temps)
            else temps
          in
          let temps = erase_past_type_arg temps in
          (* When this constructor value flows into an erased ([std::any]) slot
             ([deep_erase]) — e.g. a [Prod] pair built inside a
             value-dependent action whose result is boxed into [std::any] —
             erase its type arguments so a "cons" production's element type
             (e.g. [Prod<Nat,Nat>]) matches the canonical erased form the
             matching "nil" production produces (e.g. [Prod<any,any>]).
             Concrete field values implicitly convert to [std::any], so the
             factory call still type-checks.  This mirrors the custom-list
             element erasure in the custom-cons path, extending it to plain
             value-type constructors. *)
          let temps =
            if slot.deep_erase && temps <> [] then
              List.map index_erase_type temps
            else temps
          in
          (* The slot has already written this constructor's type down -- a
             record field declared at [SigT<std::any, std::any>], say.  At the
             positions it erased, that spelling and not the one recomputed
             from this producer's own instantiation is what the value has to
             be built at, or two producers for one field disagree about the
             erasure and neither initialises it. *)
          (* Under [deep_erase] a slot that erases nothing is this value's own
             type, not a statement about which positions are boxed. *)
          let temps =
            let slot_erases_something =
              match expected_ty with
              | Some e -> Ml_type_util.has_tany_in_type (unfold_cpp_typedef env e)
              | None -> true
            in
            if slot.deep_erase && not slot_erases_something then temps
            else temps_from_slot n temps
          in
          (* The factory has to be qualified by the very instantiation the
             declaration spells. *)
          let temps = apply_hkt_tyctors n temps in
          let temps = ind_promoted_type_args n @ temps in
          let ctor_struct = ctor_struct_name_of_ref r in
          let ind_type_name = Common.pp_global_name Type n in
          let fname =
            factory_name_of_ctor ~type_name:ind_type_name ctor_struct
          in
          (* Build: Type<temps>::factory(args).  The qualifier is a type, and
             is spelled as one: loopify reads it back off the call to build
             [make_shared], [std::get] and [typename T::Ctor] nodes, and can
             only do that if it is not hidden inside an expression. *)
          let type_expr = Tglob (n, temps, []) in
          (* A factory returns the inductive value at the very instantiation
             the qualifier spells (see [mk_factory_methods] in {!Gen_decls}),
             so the call knows its own result -- and loopify can type a frame
             field holding one instead of falling back on [decltype]. *)
          let ctor_sig args =
            Minicpp.call_sig ~yields:type_expr ~nargs:(List.length args) ()
          in
          (* Perceus reuse: if a reuse token is pending for this constructor
             (set by a use_count()==1-guarded arm in gen_cpp_case), call the
             [<factory>__reuse] variant with the token appended (stored last =
             printed first, matching the [_tok] leading parameter). *)
          ( match (!tctx).pending_reuse_token with
          | Some (tok, ctor) when globref_equal r ctor ->
            tctx := { !tctx with pending_reuse_token = None };
            let args = args @ [CPPmove tok] in
            CPPfun_call
              ( ctor_sig args,
                CPPqualified_t
                  (type_expr, Generated_name.companion (Id.of_string fname) "reuse"),
                of_reversed args )
          | _ ->
            let call =
              CPPfun_call
                ( ctor_sig args, CPPqualified_t (type_expr, Id.of_string fname),
                  of_reversed args )
            in
            if Table.is_coinductive n && not (List.for_all ml_is_value ts) then
              suspend_ctor type_expr call
            else call )
        | _ ->
          (* Fallback for non-Tglob types *)
          let ctor_struct = ctor_struct_name_of_ref r in
          let fname = factory_name_of_ctor ctor_struct in
          CPPfun_call
            (call_opaque, CPPqualified_t (Tglob (r, [], []), Id.of_string fname),
              of_reversed args )
      in
      (* [CPPfun_call] stores args reversed; [List.rev_map] compensates.
         Erased proof/type args ([MLdummy]) produce [std::any{}] — the
         corresponding C++ parameter type is [std::any] and [CPPabort]
         would throw at runtime.  The same pattern is used in
         {!gen_expr_custom_cons} for inline-extracted constructors
         (e.g., [std::make_pair]). *)
      (* Generate constructor arguments with live move_dead_after so the move
         analysis from gen_tail_expr flows through.  Safety note: gen_tail_expr
         only marks variables that occur exactly once in the entire tail
         expression (nb_occur_match = 1), so a variable appearing in multiple
         constructor args is NOT in move_dead_after and cannot be moved twice. *)
      let gen_ctor_arg ?expected_ty ?(slot = slot) e =
      match e with
        | MLdummy _ -> Cpp_erasure.empty_box
        | e when ml_value_is_void_call e ->
          wrap_void_call_as_value (gen_expr ~slot env e)
        | _ -> gen_expr ?expected_ty ~slot env e
      in
      (* When a constructor's field type is a type variable (Tvar i) that
         resolves to an owning pointer type (because T is in method_self_ns),
         the generated arg expression is a bare T value.  Wrap it so the
         field's stored type matches. *)
      (* All ML type arguments from the MLcons type — used to recover the
         actual type for fields erased to std::any when ind_nparams = 0. *)
      let ty_ml_tparams = match resolve_tmeta ty with
        | Tglob (_, tys_orig, _) -> tys_orig
        | _ -> []
      in
      (* The result type of a function-valued constructor field whose declared
         type is [Tvar i].  The [MLcons]'s own type arguments say what [i]
         stands for -- [nat -> nat], say -- so peeling off the [n_params]
         arrows the generated lambda consumes leaves the codomain.

         This is the only source for the answer: reading it back off the
         lambda that was already generated would take one branch's [return]
         for the whole function's result type.  [None] where the type
         arguments do not reach that far, as for a type-INDEXED inductive,
         which has none; each caller then supplies its own default. *)
      let field_fun_ret_ty i n_params =
        match if i >= 1 then List.nth_opt ty_ml_tparams (i - 1) else None with
        | None -> None
        | Some actual_ml_ty -> (
          match strip_tarr_n n_params (resolve_tmeta actual_ml_ty) with
          | Some ret_ml -> Some (strip_cpp_ref_const (cpp_of_ml env ret_ml))
          | None -> None )
      in
      let ctor_temps = match ty with
        | Tglob (n, tys_orig, _) ->
          let tys_filt = match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys_orig
              | None -> tys_orig )
            | _ -> tys_orig
          in
          (* At the flat arity the constructor's own instantiation is written
             at: the fields are instantiated from these, and a tail built at a
             curried element type spells a list its head does not convert
             to. *)
          (* The fields are instantiated at the arguments the call is
             printed with, so a position the call erases is erased here too. *)
          let temps =
            erase_past_type_arg
              (temps_from_slot n (template_params_of_ml ~curry:false env tys_filt))
          in
          if Table.has_dependent_params n then
            let expected_temps =
              expected_type_args_from_return env ?slot:expected_ty n
                ~arity:(List.length temps)
            in
            match expected_temps with
            | Some exp_tys ->
              List.mapi (fun i t ->
                let exp_t = normalize_erased_types (List.nth exp_tys i) in
                let is_fully_erased_fun = match exp_t with
                  | Tfun (ps, r) ->
                    List.for_all (fun p -> p = Tany) ps && r = Tany
                  | _ -> false
                in
                if t <> exp_t && (prints_as_any exp_t || is_fully_erased_fun)
                then Tany
                else if t <> exp_t then exp_t
                else if is_fully_erased_fun then Tany
                else t
              ) temps
            | None -> temps
          else temps
        | _ -> []
      in
      let field_types_raw = match Table.get_ctor_ip_types_opt r with
        | Some ft -> ft
        | None -> [] in
      let field_types =
        List.filter (fun t -> not (Mlutil.isTdummy t)) field_types_raw in
      let wrap_if_needed_for_field ft ml_e expr =
        match ft with
        | Miniml.Tvar (_, i) ->
          ( try
            let ct = List.nth ctor_temps (i - 1) in
            match ct with
            | Tshared_ptr inner ->
              let inner_g = match inner with
                | Tglob (g, _, _) -> Some g | _ -> None in
              ( match inner_g with
              | Some g when Refset'.mem g (!tctx).method_self_ns ->
                mk_call (CPPalloc (Alloc_heap, inner)) [expr]
              | _ -> expr )
            | ct when prints_as_any ct
                      || (match ct with
                          | Tglob (g, [], _) -> Table.is_erased_type_const g
                          | _ -> false) ->
              ( match expr with
              | CPPlambda
                ({ cl_params = params;
                   cl_ret = ret_ty_opt;
                   cl_body = body_stmts;
                   cl_capture = cap; _ } as lam) ->
                let params = to_reversed params in
                let n_params = List.length params in
                let new_params = List.map (fun (orig_ty, orig_id) ->
                  let bare = strip_cpp_ref_const orig_ty in
                  if bare <> Tany then (Tconst (Tref (Lvalue, Tany)), orig_id)
                  else (orig_ty, orig_id)
                ) params in
                let ml_concrete_param_tys =
                  let rec collect_lam_tys = function
                    | MLlam (_, ty, body) -> ty :: collect_lam_tys body
                    | MLmagic (_, inner) -> collect_lam_tys inner
                    | _ -> []
                  in
                  collect_lam_tys ml_e
                in
                let expand_ml_type ml_ty =
                  let abbrev r = match r with
                    | GlobRef.ConstRef kn -> Table.lookup_typedef_unchecked kn
                    | _ -> None
                  in
                  Mlutil.type_expand abbrev ml_ty
                in
                (* Canonical erased shape for a list-typed erased param is
                   [deque<std::any>] -- a bare [std::any] per element, not a
                   structure-preserving [deque<pair<any,any>>].  A sibling
                   producer for the same Coq list type (e.g. the base-case
                   action of the same [SigT] action family) may erase to the
                   flat shape; casting this parameter to the
                   structure-preserving shape would then throw
                   [std::bad_any_cast] at runtime.  See the matching
                   invariant in [gen_expr]'s [MLrel]/[MLmagic] cases. *)
                let erase_custom_list_elems = function
                  | Tglob (g, _ :: _, ns) when Ml_type_util.is_custom_list_global g ->
                    Tglob (g, [Tany], ns)
                  | t -> t
                in
                let ml_body_ret_ty =
                  let rec get_body = function
                    | MLlam (_, _, body) -> get_body body
                    | MLmagic (_, inner) -> get_body inner
                    | body -> infer_ml_body_type body
                  in
                  get_body ml_e
                in
                let erase_inner_tparams = function
                  | Tglob (g, (_ :: _), ns) when is_list_global g ->
                    (* Canonical erased shape for a list is [deque<any>],
                       a bare [std::any] per element, not a
                       structure-preserving [deque<pair<any,any>>]. *)
                    Tglob (g, [Tany], ns)
                  | Tglob (g, args, m) ->
                    let erase_t = function
                      | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
                      | _ -> Tany
                    in
                    Tglob (g, List.map erase_t args, m)
                  | t -> t
                in
                let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
                  match orig_id with
                  | None -> None
                  | Some id ->
                    let bare = strip_cpp_ref_const (fst (List.nth params j)) in
                    if bare = Tany then None
                    else
                      let concrete_ty =
                        let from_annotation =
                          match List.nth_opt ml_concrete_param_tys j with
                          | Some ml_ty ->
                            let expanded = expand_ml_type ml_ty in
                            let ct = cpp_of_ml env expanded in
                            erase_custom_list_elems (strip_cpp_ref_const ct)
                          | None -> bare
                        in
                        if not (resolves_to_any_type from_annotation) then from_annotation
                        else begin
                          let ret_ct = match ml_body_ret_ty with
                            | Some ret_ml ->
                              let ct = cpp_of_ml env ret_ml in
                              strip_cpp_ref_const ct
                            | None -> Tany
                          in
                          erase_inner_tparams ret_ct
                        end
                      in
                      if resolves_to_any_type concrete_ty then None
                      else
                        let any_id = Id.of_string ("_any_" ^ Id.to_string id) in
                        Some (id, any_id, concrete_ty)
                ) (List.mapi (fun idx p -> (idx, p)) new_params) in
                let new_body =
                  List.fold_left (fun stmts (orig_id, any_id, concrete_ty) ->
                    let cast_stmt = Sasgn (orig_id, Declare concrete_ty,
                      Cpp_erasure.unbox concrete_ty (CPPvar any_id)) in
                    cast_stmt :: stmts
                  ) body_stmts (List.rev cast_bindings)
                in
                let renamed_params = List.map (fun (ty, id_opt) ->
                  match id_opt with
                  | Some id ->
                    (match List.find_opt (fun (oid, _, _) -> Id.equal oid id) cast_bindings with
                     | Some (_, any_id, _) -> (ty, Some any_id)
                     | None -> (ty, id_opt))
                  | None -> (ty, id_opt)
                ) new_params in
                let erased_ret_ty =
                  match field_fun_ret_ty i n_params with
                  | Some t -> t
                  | None -> Tany
                in
                let new_ret_ty = match ret_ty_opt with
                  | Some _ -> ret_ty_opt
                  | None -> if erased_ret_ty <> Tany then Some erased_ret_ty else None
                in
                let new_lambda = erased_lambda lam
                    ~params:(of_reversed renamed_params)
                    ~ret:new_ret_ty
                    ~body:new_body in
                (* The field itself is fully erased, so the only signature a
                   consumer can cast back to is the canonical
                   [std::function<std::any(std::any...)>] -- the same one the
                   non-lambda case below stores.  The lambda keeps its own
                   concrete result type; [crane_erase_fn] deduces it and boxes
                   what it returns. *)
                wrap_crane_erase_fn new_lambda
              | _ ->
                (* When a custom list literal (e.g. deque<Val>) is stored in a
                   std::any field, regenerate it with [deep_erase] so
                   elements are erased to std::any.  The stored value becomes
                   deque<any>, matching what any_cast<deque<any>> expects when
                   consuming through the erased field. *)
                let rec is_custom_list_cons = function
                  | MLcons (_, GlobRef.ConstructRef ((kn, _), _), _) ->
                    let ind = GlobRef.IndRef (kn, 0) in
                    Ml_type_util.is_custom_list_global ind
                  | MLmagic (_, inner) -> is_custom_list_cons inner
                  | _ -> false
                in
                if is_custom_list_cons ml_e then begin
                  gen_ctor_arg ~slot:{slot with deep_erase = true} ml_e
                end else begin
                  (* A non-lambda FUNCTION value (e.g. a forwarded callback
                     parameter [f]) stored into an erased field must be wrapped
                     into the canonical [std::function<std::any(std::any...)>]
                     representation that the application side reads back with
                     [any_cast<std::function<std::any(std::any)>>] (see
                     [eta_fun]'s [callee_is_bare_any] branch).  Storing the raw
                     closure makes the [std::any] hold the bare lambda type, so
                     that [any_cast] throws at runtime.

                     The domain/codomain of such a function are typically
                     value-dependent (erased to [std::any] in the generic ML
                     type), so the concrete argument types needed for the
                     [any_cast] inside the adapter are only known at C++
                     instantiation.  Rather than reconstruct them here, defer to
                     the [crane_erase_fn] runtime helper, which uses
                     [std::function] CTAD to deduce the callable's signature and
                     builds the [std::function<std::any(std::any...)>] adapter
                     (unbox each argument, box the result). *)
                  (* Wrap via the [crane_erase_fn] runtime helper (emitted as
                     [#include "crane_fn.h"] in the header preamble). *)
                  erase_fn_for_any_slot ml_e expr
                end )
            | Tfun (param_tys, ret_ty) when List.exists (fun t -> t = Tany) param_tys ->
              ( match expr with
              | CPPlambda
                ({ cl_params = params;
                   cl_ret = ret_ty_opt;
                   cl_body = body_stmts;
                   cl_capture = cap; _ } as lam) ->
                let params = to_reversed params in
                let n_params = List.length params in
                let new_params = List.mapi (fun j (orig_ty, orig_id) ->
                  if j < List.length param_tys && List.nth param_tys j = Tany then
                    let bare = strip_cpp_ref_const orig_ty in
                    if bare <> Tany then (Tconst (Tref (Lvalue, Tany)), orig_id)
                    else (orig_ty, orig_id)
                  else (orig_ty, orig_id)
                ) params in
                let ml_body_ret_ty =
                  let rec get_body = function
                    | MLlam (_, _, body) -> get_body body
                    | MLmagic (_, inner) -> get_body inner
                    | body -> infer_ml_body_type body
                  in
                  get_body ml_e
                in
                let ml_concrete_param_tys =
                  let rec collect_lam_tys = function
                    | MLlam (_, ty, body) -> ty :: collect_lam_tys body
                    | MLmagic (_, inner) -> collect_lam_tys inner
                    | _ -> []
                  in
                  collect_lam_tys ml_e
                in
                let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
                  if j < List.length param_tys && List.nth param_tys j = Tany then
                    match orig_id with
                    | None -> None
                    | Some id ->
                      let concrete_ty =
                        let from_annotation =
                          match List.nth_opt ml_concrete_param_tys j with
                          | Some ml_ty ->
                            let ct = cpp_of_ml env ml_ty in
                            strip_cpp_ref_const ct
                          | None -> Tany
                        in
                        if not (resolves_to_any_type from_annotation) then
                          from_annotation
                        else begin
                          let ret_ct = match ml_body_ret_ty with
                          | Some ret_ml ->
                            let ct = cpp_of_ml env ret_ml in
                            strip_cpp_ref_const ct
                          | None -> Tany
                          in
                          let erase_inner_tparams = function
                            | Tglob (g, args, m) ->
                              let erase_t = function
                                | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
                                | _ -> Tany
                              in
                              Tglob (g, List.map erase_t args, m)
                            | t -> t
                          in
                          erase_inner_tparams ret_ct
                        end
                      in
                      (* Canonical erased shape for a list-typed erased param
                         is [deque<std::any>] -- a bare [std::any] per
                         element, not a structure-preserving
                         [deque<pair<any,any>>].  See the matching invariant
                         in [gen_expr]'s [MLrel]/[MLmagic] cases. *)
                      let concrete_ty =
                        match concrete_ty with
                        | Tglob (g, _ :: _, ns) when is_list_global g ->
                          Tglob (g, [Tany], ns)
                        | Tnamespace (ns_g, Tglob (g, _ :: _, ns))
                          when is_list_global g ->
                          Tnamespace (ns_g, Tglob (g, [Tany], ns))
                        | t -> t
                      in
                      if resolves_to_any_type concrete_ty then None
                      else
                        let any_id = Id.of_string ("_any_" ^ Id.to_string id) in
                        Some (id, any_id, concrete_ty)
                  else None
                ) (List.mapi (fun idx p -> (idx, p)) new_params) in
                let new_body =
                  List.fold_left (fun stmts (orig_id, any_id, concrete_ty) ->
                    let cast_stmt = Sasgn (orig_id, Declare concrete_ty,
                      Cpp_erasure.unbox concrete_ty (CPPvar any_id)) in
                    cast_stmt :: stmts
                  ) body_stmts (List.rev cast_bindings)
                in
                let renamed_params = List.map (fun (ty, id_opt) ->
                  match id_opt with
                  | Some id ->
                    (match List.find_opt (fun (oid, _, _) -> Id.equal oid id) cast_bindings with
                     | Some (_, any_id, _) -> (ty, Some any_id)
                     | None -> (ty, id_opt))
                  | None -> (ty, id_opt)
                ) new_params in
                let erased_param_tys = List.map (fun _ -> Tany) renamed_params in
                let erased_ret_ty =
                  match field_fun_ret_ty i n_params with
                  | Some t -> t
                  | None -> Tany
                in
                let new_ret_ty = match ret_ty_opt with
                  | Some _ -> ret_ty_opt
                  | None -> if erased_ret_ty <> Tany then Some erased_ret_ty else None
                in
                let new_lambda = erased_lambda lam
                    ~params:(of_reversed renamed_params)
                    ~ret:new_ret_ty
                    ~body:new_body in
                let func_ty = Tfun (safe_firstn n_params erased_param_tys, erased_ret_ty) in
                Cpp_erasure.converting_ctor func_ty [new_lambda]
              (* A function value that is not a lambda literal (a reference to a
                 global, or a methodified one) cannot have its parameters
                 rewritten the way the branch above rewrites a literal's, so
                 defer the adaptation to the runtime helper, which deduces the
                 callable's signature and unboxes each argument.  The field's
                 own codomain stays concrete. *)
              | _ when ml_expr_is_function_value ml_e ->
                wrap_crane_erase_fn
                  ?ret_ty:(if ret_ty = Tany then None else Some ret_ty)
                  expr
              | _ -> expr )
            | _ -> expr
            with Failure _ | Invalid_argument _ ->
              (* Field type index is beyond ctor_temps — this field is erased
                 to std::any.  If the expression is a lambda, wrap it in
                 std::function so that std::any stores the type-erased wrapper
                 and any_cast<std::function<...>> can recover it. *)
              match expr with
              | CPPlambda
                { cl_params = params;
                  cl_ret = ret_ty_opt;
                  cl_body = body_stmts;
                  _ } ->
                let params = to_reversed params in
                let param_types = List.map (fun (ty, _) ->
                  strip_cpp_ref_const ty) params in
                let ret_ty = match ret_ty_opt with
                  | Some ty -> strip_cpp_ref_const ty
                  | None ->
                    ( match
                        field_fun_ret_ty i (List.length param_types)
                      with
                    | Some t -> t
                    | None -> Tvoid )
                in
                Cpp_erasure.converting_ctor (Tfun (param_types, ret_ty)) [expr]
              | _ -> expr )
        | ft ->
          (* Handle arrow types containing erased type variables.
             E.g. field type Tarr(Tvar 1, Tglob(nat)) where Tvar 1 is erased:
             the concrete lambda [](uint64_t x){return x*x;} must become
             [](std::any _a0){return any_cast<uint64_t>(_a0) * any_cast<uint64_t>(_a0);}
             so it matches the factory param std::function<uint64_t(std::any)>. *)
          let tvar_is_erased i =
            try match List.nth ctor_temps (i - 1) with
              | Tany -> true | _ -> false
            with Failure _ | Invalid_argument _ -> true
          in
          let rec ft_has_erased_tvar = function
            | Miniml.Tvar (_, i) -> tvar_is_erased i
            | Miniml.Tunknown -> true
            (* A type computed from a value -- [memCType c] -- erases to
               [std::any] as surely as an erased variable does. *)
            | Miniml.Tglob (g, _, _)
              when Table.is_value_dep_type_scheme g || Table.is_erased_type_const g ->
              true
            | Miniml.Tarr (a, b) -> ft_has_erased_tvar a || ft_has_erased_tvar b
            | _ -> false
          in
          ( match ft, expr with
          | Miniml.Tarr _, CPPlambda
            ({ cl_params = params;
               cl_ret = ret_ty_opt;
               cl_body = body_stmts;
               cl_capture = cap; _ } as lam)
            when ft_has_erased_tvar ft ->
            let params = to_reversed params in
            let rec collect_tarr = function
              | Miniml.Tarr (a, rest) ->
                let (ps, r) = collect_tarr rest in (a :: ps, r)
              | t -> ([], t)
            in
            let (ml_param_tys, ml_ret_ty) = collect_tarr ft in
            (* The field's type is written in the inductive's variables, not
               this scope's: [k : X -> T] names the constructor's third
               parameter, which this call instantiates through [ctor_temps]. *)
            let erase_ml_ty t =
              match t with
              | Miniml.Tvar (_, i) when tvar_is_erased i -> Tany
              | Miniml.Tunknown -> Tany
              | _ ->
                subst_cpp_tvars
                  (fun i -> if i >= 1 then List.nth_opt ctor_temps (i - 1) else None)
                  (cpp_of_ml env t)
            in
            let erased_param_tys = List.map erase_ml_ty ml_param_tys in
            let erased_ret_ty = erase_ml_ty ml_ret_ty in
            let n_params = List.length params in
            (* Build new params with std::any for erased positions, and add
               any_cast let-bindings for each erased parameter at the start
               of the body. *)
            let new_params = List.mapi (fun j (orig_ty, orig_id) ->
              let erased_ty =
                if j < List.length erased_param_tys
                   && List.nth erased_param_tys j = Tany
                   && strip_cpp_ref_const orig_ty <> Tany
                then
                  (* Replace concrete type with std::any, preserving const ref *)
                  Tconst (Tref (Lvalue, Tany))
                else orig_ty
              in
              (erased_ty, orig_id)
            ) params in
            (* Extract concrete parameter types from the MiniML lambda *)
            let ml_concrete_param_tys =
              let rec collect_lam_tys = function
                | MLlam (_, ty, body) -> ty :: collect_lam_tys body
                | MLmagic (_, inner) -> collect_lam_tys inner
                | _ -> []
              in
              collect_lam_tys ml_e
            in
            let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
              if j < List.length erased_param_tys
                 && List.nth erased_param_tys j = Tany then
                match orig_id with
                | Some id ->
                  (* Get concrete type from ML lambda param, not C++ lambda *)
                  let concrete_ty =
                    match List.nth_opt ml_concrete_param_tys j with
                    | Some ml_ty ->
                      let ct = cpp_of_ml env ml_ty in
                      strip_cpp_ref_const ct
                    | None -> strip_cpp_ref_const (fst (List.nth params j))
                  in
                  (* Canonical erased shape for a list-typed erased param is
                     [deque<std::any>] -- a bare [std::any] per element -- not
                     a structure-preserving [deque<pair<any,any>>].  A sibling
                     producer for the same Coq list type (e.g. the base-case
                     action of the same [SigT] action family) may erase to
                     the flat shape; casting this parameter to the
                     structure-preserving shape would then throw
                     [std::bad_any_cast] at runtime.  See the matching
                     invariant in [gen_expr]'s [MLrel]/[MLmagic] cases. *)
                  let concrete_ty =
                    match concrete_ty with
                    | Tglob (g, _ :: _, ns) when is_list_global g ->
                      Tglob (g, [Tany], ns)
                    | Tnamespace (ns_g, Tglob (g, _ :: _, ns))
                      when is_list_global g ->
                      Tnamespace (ns_g, Tglob (g, [Tany], ns))
                    | t -> t
                  in
                  (* [Topaque] is no more castable than [Tany]: both print
                     as [std::any], and neither names a representation to
                     recover the parameter into. *)
                  if (not (prints_as_any concrete_ty)) && concrete_ty <> Tauto
                  then
                    let any_param_id = Id.of_string
                      ("_any_" ^ Id.to_string id) in
                    Some (j, id, any_param_id, concrete_ty)
                  else None
                | None -> None
              else None
            ) (List.mapi (fun j p -> (j, p)) params) in
            let new_params = List.mapi (fun j (ty, id) ->
              match List.find_opt (fun (j', _, _, _) -> j = j') cast_bindings with
              | Some (_, _, any_id, _) -> (ty, Some any_id)
              | None -> (ty, id)
            ) new_params in
            let cast_stmts = List.map (fun (_, orig_id, any_id, concrete_ty) ->
              Sasgn (orig_id, Declare concrete_ty,
                Cpp_erasure.unbox concrete_ty (CPPvar any_id))
            ) cast_bindings in
            let new_body = cast_stmts @ body_stmts in
            let new_ret_ty = match ret_ty_opt with
              | Some _ -> ret_ty_opt
              | None -> if erased_ret_ty <> Tany then Some erased_ret_ty else None
            in
            let new_lambda = erased_lambda lam
                ~params:(of_reversed new_params)
                ~ret:new_ret_ty
                ~body:new_body in
            let func_ty = Tfun (safe_firstn n_params erased_param_tys, erased_ret_ty) in
            Cpp_erasure.converting_ctor func_ty [new_lambda]
          (* The same erased-argument adaptation, for a function value that is
             not a lambda literal (a reference to a global, or to a method):
             there are no parameters here to rewrite, so defer to the runtime
             helper, which deduces the callable's signature and unboxes each
             argument.  The field's codomain stays concrete. *)
          | Miniml.Tarr _, _ when ft_has_erased_tvar ft && ml_expr_is_function_value ml_e ->
            let rec codomain = function
              | Miniml.Tarr (_, rest) -> codomain rest
              | t -> t
            in
            let ret_ty = cpp_of_ml env (codomain ft) in
            let expr = erased_fn_instantiation expr in
            wrap_crane_erase_fn
              ?ret_ty:(if prints_as_any ret_ty then None else Some ret_ty)
              expr
          | _ -> expr )
      in
      let gen_and_wrap i e =
        let ft_opt, expr =
          (* A constructor argument returns its own value, not the enclosing
             function's, so the ambient return type must not reach it. *)
          with_cpp_return_type None (fun () ->
          let ft_opt =
            try Some (List.nth field_types i)
            with Failure _ | Invalid_argument _ -> None
          in
          (* A constructor field with a CONCRETE type receiving an argument that
             is an erased ([std::any]) pattern variable (e.g. a leaf destructured
             from a deeply-erased [pair<any,any>] via [any_cast]) needs a final
             [any_cast<concrete>] — otherwise the bare [std::any] is forwarded
             straight into a concrete-typed factory parameter and fails to
             compile.  Thread the field's concrete C++ type as the expected type
             so the erased-[MLrel] path (see [gen_expr]'s [MLrel] case) inserts
             the cast.  [Tvar] fields are left to
             [wrap_if_needed_for_field], which handles the erased-field cases. *)
          (* The field's declared type with this constructor call's own type
             arguments substituted in — the [P] of [sigT A P] becomes the
             concrete C++ type the field holds at this call site. *)
          let instantiated_field_cpp_ty ft =
            subst_cpp_tvars
              (fun i -> if i >= 1 then List.nth_opt ctor_temps (i - 1) else None)
              (cpp_of_ml env ft)
          in
          let expected_for_arg =
            match ft_opt with
            | Some ft ->
              let is_erased_rel =
                match e with
                | MLrel j | MLmagic (_, MLrel j) ->
                  binder_is_boxed j
                | _ -> false
              in
              ( match ft with
              | (Miniml.Tvar (_, _))
                when (match unfold_cpp_typedef env (instantiated_field_cpp_ty ft) with
                      | Tglob (_, args, _) ->
                        args <> [] && List.exists has_tany_in_type args
                      | _ -> false) ->
                (* An element type the slot has already erased.  A nested
                   constructor has to be built at that same instantiation --
                   [SigT<any, any>], not [SigT<any, Nat>] -- or the value it
                   produces does not convert into the container holding it. *)
                Some (unfold_cpp_typedef env (instantiated_field_cpp_ty ft))
              (* A boxed variable at a type-parameter field -- [Ret x] with [x]
                 the erased existential of the continuation it is in -- is
                 recovered at the field's instantiation. *)
              | Miniml.Tvar (_, _)
                when is_erased_rel
                     && not (prints_as_any (instantiated_field_cpp_ty ft)) ->
                Some (instantiated_field_cpp_ty ft)
              (* A value constructed straight into a type-parameter field --
                 [retf ((m, (ls, g')), r)] -- is spelled here for the first
                 time, and the field's instantiation, where the destination
                 wrote it in full, is the type to build it at: its own
                 annotation may erase a class variable the field writes. *)
              | Miniml.Tvar (_, _)
                when (match strip_magic e with MLcons _ -> true | _ -> false)
                     && (let ct = instantiated_field_cpp_ty ft in
                         (not (has_tany_in_type ct)) && names_only_scoped_tvars ct) ->
                Some (instantiated_field_cpp_ty ft)
              | Miniml.Tvar (_, _) -> None
              | Miniml.Tapp _ ->
                (* A field that applies one of the inductive's [template
                   <typename> class] parameters ([F A]).  Nothing in the
                   argument names the instantiation -- a [None] has no value to
                   read it off -- so it can only come from this call's own type
                   arguments.  The substitution is done on the ML type: only
                   there does applying [option] to [nat] reduce, since the C++
                   side of a custom-extracted [option] is a template string. *)
                let ct = cpp_of_ml env (Mlutil.type_subst_list ty_ml_tparams ft) in
                if prints_as_any ct || has_tany_in_type ct then None else Some ct
              | _ when is_erased_rel ->
                let ct = cpp_of_ml env ft in
                if prints_as_any ct then None else Some ct
              | Miniml.Tglob (g, _, _)
                when (match resolve_tmeta ty with
                     | Miniml.Tglob (n_ind, _, _) -> globref_equal g n_ind
                     | _ -> false)
                     || ( match strip_magic e with
                        | MLcons (_, GlobRef.ConstructRef ((kn, i), _), _) ->
                          globref_equal g (GlobRef.IndRef (kn, i))
                        | _ -> false ) ->
                (* The recursive spine: every cell of a list is the same C++
                   type, so the tail is built at the instantiation this cell
                   was, not at the one its own annotation converts to.  So is
                   a constructor built straight into a field of its own type
                   -- [go (RetF r)] -- whose annotation may have lost an
                   argument MiniML erases, a family, that the field states.
                   A family variable is written applied at an erased index
                   ([T1<std::any>], taken back off where it is declared
                   plain), and that erasure is no reason to refuse the field:
                   only an erased argument outside such an application is.
                   The spine keeps its stricter test, which it was written
                   with. *)
                let rec erased_outside_family_apps t =
                  match t with
                  | Tapply (Tvar _, _) -> false
                  | Tglob (_, args, _) | Tapply (_, args) ->
                    List.exists erased_outside_family_apps args
                  | Tfun (ps, r) ->
                    List.exists erased_outside_family_apps (r :: ps)
                  | Tshared_ptr t | Tconst t | Tref (_, t) | Tnamespace (_, t) ->
                    erased_outside_family_apps t
                  | t -> prints_as_any t
                in
                let ct = instantiated_field_cpp_ty ft in
                let spine =
                  match resolve_tmeta ty with
                  | Miniml.Tglob (n_ind, _, _) -> globref_equal g n_ind
                  | _ -> false
                in
                if (if spine then has_tany_in_type ct
                    else erased_outside_family_apps ct)
                then None
                else Some ct
              | _ ->
                (* A field whose instantiated C++ type is a curried function
                   (e.g. [A -> A] at [A = nat -> nat]) must keep its currying:
                   without the expected type, [gen_expr]'s [MLlam] case would
                   flatten the nested binders into one multi-parameter lambda,
                   which does not convert to [std::function<F(F)>]. *)
                let ct = instantiated_field_cpp_ty ft in
                ( match (ft, ct) with
                | _, Tfun (_, Tfun _) when not (prints_as_any ct) -> Some ct
                (* A lambda built into a function-typed field -- [VisF]'s
                   continuation -- is written against the field: its result
                   is what the body's constructors are built at. *)
                | _, Tfun (_, cod)
                  when (match strip_magic e with MLlam _ -> true | _ -> false)
                       && not (prints_as_any cod) ->
                  Some ct
                | _ -> (
                  (* The same rule the bare-parameter case above states, for a
                     field that names a type of its own: where the field's
                     spelling erases some of its arguments and keeps others,
                     that spelling is the only statement of which are which,
                     and the value has to be built at it. *)
                  let u = unfold_cpp_typedef env ct in
                  match u with
                  | Tglob (_, (_ :: _ as args), _)
                    when List.exists prints_as_any args
                         && not (List.for_all prints_as_any args) ->
                    Some u
                  | _ -> None ) ) )
            | None -> None
          in
          (* When a function value is stored into an erased ([std::any])
             constructor field (e.g. the action [unit -> semty s] stored in a
             heterogeneous [sigT] list), the function's return value is, at
             runtime, boxed inside a single [std::any].  Consumers recover it
             with a fixed [any_cast] shape, so ALL of a given Coq type's
             producers must erase to the SAME canonical C++ representation.  For
             [list (nat*nat)] the empty ("nil") production erases to
             [deque<pair<any,any>>] (its element type is already opaque in the
             ML annotation), whereas a non-empty ("cons") production built from
             concrete pair values would otherwise stay [deque<Prod<Nat,Nat>>] --
             a different C++ type for the same Coq type, causing
             [std::bad_any_cast] at the consumer.  Generate the body with
             [deep_erase] so cons productions deep-erase their element
             type to match nil.  See the mirror in the record-constructor path. *)
          (* The same field type on the ML side.  A field's declared type says
             nothing on its own -- a bare parameter ([A]) or an applied one
             ([F A]) names the inductive's variables, not this value's types --
             but substituting the constructor's own type arguments turns it
             into the [option (nat -> nat)] the argument is actually built at,
             which is finer than the slot's expectation (that one states the
             whole inductive, not this field).  An applied parameter is taken
             unconditionally, as it always resolved that way; for any other
             field the substitution is only an improvement when it left neither
             erasure nor a stray type variable behind.  Otherwise the slot is
             the better guess, but only for a field of the inductive's own
             type -- the recursive spine, where the slot does state the field.
             Any other field is not what the slot states, and a constructor
             built in it would take the enclosing one's type for its own. *)
          let expected_ml_for_arg =
            match ft_opt with
            | Some ft -> (
              let inst = Mlutil.type_subst_list ty_ml_tparams ft in
              match ft with
              | Miniml.Tapp _ -> Some inst
              | _
                when (not (ml_type_contains_erased ~in_arrows:true inst))
                     && not (Ml_type_util.ml_type_contains_tvar inst) ->
                Some inst
              | Miniml.Tglob (g, _, _)
                when ( match resolve_tmeta ty with
                     | Miniml.Tglob (n_ind, _, _) -> globref_equal g n_ind
                     | _ -> false ) ->
                slot.expected_ml_ty
              | _ -> None )
            | None -> slot.expected_ml_ty
          in
          let expr =
            gen_ctor_arg
              ~slot:
                { slot with
                  expected_ml_ty = expected_ml_for_arg;
                  deep_erase =
                    slot.deep_erase
                    || field_stores_erased_fn_value
                         ?field_cpp_ty:(Option.map instantiated_field_cpp_ty ft_opt)
                         field_types i e }
              ?expected_ty:expected_for_arg e
          in
            (ft_opt, expr) )
        in
        let expr =
          match ft_opt with
          | Some ft -> wrap_if_needed_for_field ft e expr
          | None -> expr
        in
        let expr =
          match ft_opt with
          | Some ft -> container_cast_erased_field ft e expr
          | None -> expr
        in
        expr
      in
      gen_ctor_call (List.rev (List.mapi gen_and_wrap ts_updated))
    | _ ->
      (* Records: a record struct erases the promoted variables it does not
         take as parameters to [std::any], so a lambda assigned to one of its
         fields has to spell them that way too, and the scope forgets how to
         resolve them.  The ones it mentions without declaring are parameters
         of the struct like any other inductive's (see
         {!ind_promoted_type_args}), so its fields spell them resolved, and so
         must everything built for them here. *)
      let mentioned =
        match ty with Tglob (n, _, _) -> Table.promoted_type_params n | _ -> []
      in
      tctx :=
        { !tctx with
          promoted_var_map =
            List.filter
              (fun (v, _) -> List.exists (Id.equal v) mentioned)
              (!tctx).promoted_var_map };
      let nstempmod args =
        match ty with
        | Tglob (n, tys, _) ->
          (* Filter out index type args - only keep parameters *)
          let tys =
            match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys
              | None -> tys )
            | _ -> tys
          in
          (* Named against the enclosing scope's type variables.  Inside an
             instance member template a recovered [Tvar 3] is the method's
             own [_A0], and an empty name list spells it as the anonymous
             [T3] -- a free name where the erasure at least compiled. *)
          let temps = ind_promoted_type_args n @ template_params_of_ml env tys in
          if Table.is_coinductive n then
            mk_call
              (CPPalloc (Alloc_heap, Tglob (n, temps, [])))
              [CPPstruct (n, temps, args)]
          else
            (* Value-type records: direct construction, no make_shared *)
            CPPstruct (n, temps, args)
        | _ ->
          CErrors.anomaly
            (Pp.str
               "gen_expr: non-record MLcons with matching type expected Tglob" )
      in
      (* Defense-in-depth: same safeguard as for non-record constructors above *)
      let saved_dead = (!tctx).move_dead_after in
      tctx := { !tctx with move_dead_after = Escape.IntSet.empty };
      let record_arg_exprs =
        (* A record's erased fields (a promoted [Type] field such as [dyn]'s
           [dty]) carry no argument, so the declared field types are aligned
           with the arguments only once the [Tdummy] entries are dropped --
           otherwise every field from the first erased one on is read off by
           the type of its predecessor. *)
        let field_types_rec =
          match Table.get_ctor_ip_types_opt r with
          | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
          | None -> []
        in
        let tvars = get_current_type_vars () in
        (* A record field with a CONCRETE type receiving an argument that is an
           erased ([std::any]) pattern variable (e.g. a leaf destructured from a
           deeply-erased [pair<any,any>]) needs a final [any_cast<concrete>] —
           otherwise the bare [std::any] is aggregate-brace-initialized into a
           concrete field and fails to compile.  Thread the field's concrete C++
           type as the expected type so the erased-[MLrel] path (see [gen_expr]'s
           [MLrel] case) inserts the cast.  This mirrors the equivalent handling
           for value-type (variant) constructors in [gen_and_wrap]. *)
        let expected_for_field i e =
          match List.nth_opt field_types_rec i with
          | Some ft ->
            let is_erased_rel =
              match e with
              | MLrel j | MLmagic (_, MLrel j) ->
                binder_is_boxed j
              | _ -> false
            in
            ( match ft with
            | Miniml.Tvar (_, _) -> None
            | _ when is_erased_rel ->
              let ct = cpp_of_ml env ft in
              if prints_as_any ct then None else Some ct
            (* A call is the field's value: its result is the field's type at
               this record's arguments -- [tfmap f (g_exp g)] into [g_exp :
               option (exp T)] at an erased [T] is an
               [std::optional<exp<std::any>>], which fills the carrier a
               bare-variable codomain cannot. *)
            | _ when (match strip_magic e with MLapp _ -> true | _ -> false) -> (
              match ty with
              | Miniml.Tglob (_, tys, _) ->
                let ct = cpp_of_ml env (Mlutil.type_subst_list tys ft) in
                if prints_as_any ct || not (names_only_scoped_tvars ct) then None
                else Some ct
              | _ -> None )
            | _ -> None )
          | None -> None
        in
        (* The type the struct declares a field at: a record that renders no
           template parameter erases every type variable left in its field
           types (see [gen_ind_header_v2]), so that -- not the conversion that
           keeps the variable -- is the type an argument reaches the field
           at. *)
        let declared_field_cpp_ty ft =
          match ty with
          | Tglob ((GlobRef.IndRef (kn, _) as n), _, _) ->
            let t =
              convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton n) tvars ft
            in
            if Table.get_ind_num_param_vars_opt kn = Some 0 then
              Ml_type_util.tvar_erase_type t
            else t
          | _ -> cpp_of_ml env ft
        in
        (* A field the struct declares at an erased instantiation -- a
           [sigT] whose witness type the record erased, so
           [SigT<std::any, std::any>] -- accepts only a value built at that
           same instantiation.  Each producer would otherwise build its own
           ([SigT<std::any, List<std::any>>] for a list payload), which is a
           different C++ type and does not initialise the field.  Generating
           the argument with [deep_erase] boxes its components, so every
           producer arrives at the one shape the field is declared at. *)
        let field_declared_erased i =
          match List.nth_opt field_types_rec i with
          | Some ft -> (
            (* The alias has to come off first: [texp<std::any>] looks fully
               erased at its own one argument and is not -- the [std::pair] it
               stands for keeps a concrete second component. *)
            match
              Ml_type_util.unqualify_ty
                (unfold_cpp_typedef env (declared_field_cpp_ty ft))
            with
            | Tglob (_, (_ :: _ as args), _) as d
              when List.for_all
                     (fun a ->
                       prints_as_any a || Ml_type_util.is_cpp_dummy_type a )
                     args
                   && List.exists prints_as_any args ->
              Some d
            | _ -> None )
          | None -> None
        in
        let arg_slot = {slot with in_ctor_arg = true} in
        let base_args =
          List.mapi
            (fun i e ->
              match e with
              | e when ml_value_is_void_call e ->
                wrap_void_call_as_value (gen_expr ~slot:arg_slot env e)
              | _ ->
                gen_expr
                  ~slot:
                    { arg_slot with
                      deep_erase =
                        arg_slot.deep_erase
                        || field_stores_erased_fn_value field_types_rec i e }
                  ?expected_ty:
                    ( match expected_for_field i e with
                    | Some _ as t -> t
                    | None -> field_declared_erased i )
                  env e)
            ts
        in
        match ty with
        | Tglob (n, _, _) ->
          let field_types = field_types_rec in
          List.mapi
            (fun i expr ->
              match List.nth_opt field_types i with
              | Some ft ->
                (* An erased list leaf forwarded into a concrete-element list
                   field (e.g. [mkRec ts] with field [items : deque<elt>]) came
                   out as the erased [deque<std::any>]; convert it to the
                   concrete-element container before aggregate initialization. *)
                let expr =
                  match List.nth_opt ts i with
                  | Some e -> container_cast_erased_field ft e expr
                  | None -> expr
                in
                let storage_ty =
                  convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton n) tvars ft
                in
                let api_ty =
                  cpp_of_ml env ft
                in
                (* A closure written at the concrete domain does not convert
                   to the erased signature the field is declared at; [coerce]
                   supplies the [crane_erase_fn] adapter. *)
                let declared_ty = declared_field_cpp_ty ft in
                let expr =
                  if erased_domain_fun_ty declared_ty then
                    coerce ?term:(List.nth_opt ts i) ~into:declared_ty expr
                  else expr
                in
                wrap_storage_expr ~storage_ty ~api_ty expr
              | None -> expr)
            base_args
        | _ -> base_args
      in
      let result = nstempmod record_arg_exprs in
      tctx := { !tctx with move_dead_after = saved_dead };
      result
    in
    cons_result
  | MLcase (typ, t, pv) when is_custom_match pv ->
    let iife_ret =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = cpp_of_ml env branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_void_call branch_rty
      then Tvoid else r
    in
    let stmts =
      let ret =
        if iife_ret = Tvoid then Some Tvoid
        else (!tctx).current_cpp_return_type
      in
      with_cpp_return_type ret (fun () ->
          gen_custom_cpp_case env (fun x -> Sreturn (Some x)) typ t pv )
    in
    mk_iife (Some iife_ret) stmts
  | MLcase (typ, t, pv)
    when (not (record_fields_of_type typ == [])) && Array.length pv == 1 ->
    let ids, r, pat, body = pv.(0) in
    let n = List.length ids in
    let is_typeclass = Table.is_typeclass_type typ in
    (* Build lists that correctly account for erased fields.
       record_fields_of_type includes None entries for erased fields; ids only
       contains non-erased bindings. So MLrel i refers to the i-th non-erased
       field. We filter out None entries for correct indexing. *)
    let all_fields = record_fields_of_type typ in
    let non_erased_fields = List.filter_map Fun.id all_fields in
    let all_field_types =
      match typ with
      | Tglob (r, _, _) -> Table.record_field_types r
      | _ -> []
    in
    let non_erased_field_types =
      filter_value_types all_field_types
    in
    let record_ref_opt =
      match typ with Tglob (r, _, _) -> Some r | _ -> None
    in
    let wrap_record_field_to_api idx access =
      match (record_ref_opt, List.nth_opt non_erased_field_types idx) with
      | Some record_ref, Some ml_ty ->
        let tvars = get_current_type_vars () in
        let storage_ty =
          convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton record_ref)
            tvars
            ml_ty
        in
        let api_ty =
          cpp_of_ml env ml_ty
        in
        wrap_api_expr ~storage_ty ~api_ty access
      | _ -> access
    in
    (* For type classes, use qualified access (::) instead of arrow (->) since
       type class instances are template type parameters, not runtime values *)
    let make_field_access base_expr fld =
      if is_typeclass then
        let fld_name = Common.id_of_global Term fld in
        CPPscope (base_expr, fld_name, [])
      else
        CPPget' (base_expr, fld, record_field_cpp_ty env typ fld)
    in
    (* Strip MLmagic wrappers from the body — promoted dependent records may
       wrap field references in MLmagic due to Tvar/Tglob mismatches *)
    let body' =
      match body with
      | MLmagic (_, b) -> b
      | b -> b
    in
    ( match body' with
    | MLrel i when i <= n ->
      let fld =
        try Some (List.nth non_erased_fields (n - i)) with _ -> None
      in
      ( match fld with
      | Some fld ->
        let access = make_field_access (gen_expr env t) fld in
        let access = wrap_record_field_to_api (n - i) access in
        if is_typeclass then
          (* For typeclasses, non-function value fields (like m_id : carrier)
             are generated as nullary static methods, so we need () to call
             them *)
          let fld_ty =
            try List.nth non_erased_field_types (n - i)
            with _ -> Miniml.Tunknown
          in
          let is_value_field =
            match fld_ty with
            | Miniml.Tarr _ -> false
            (* A field whose type is itself a typeclass (a superclass field)
               is promoted to a type alias in the instance struct
               ([using ord_eq = eqnat;]), not to a nullary static method, so
               calling it would emit [I::ord_eq()].  It is only ever used as
               a nested-name-specifier for the superclass's projections. *)
            | _ when Table.is_typeclass_type fld_ty -> false
            | _ -> true
          in
          if is_value_field then
            mk_call access []
          else
            access
        else
          access
      | _ ->
        CErrors.anomaly (Pp.str "record field index out of bounds") )
    | MLapp ((MLrel i | MLmagic (_, MLrel i)), args) when i <= n ->
      let fld =
        try Some (List.nth non_erased_fields (n - i)) with _ -> None
      in
      let branch_binders =
        List.rev_map (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty)) ids
      in
      let _, env' = push_vars' branch_binders env in
      ( match fld with
      (* [CPPfun_call] expects args in reverse order; [List.rev_map] both
         converts and reverses.  Filter [MLdummy] args — these are erased type
         parameters (e.g. [A : Type] in [f : forall A, A -> A]) with no C++
         runtime representation.  When the field's codomain erases to [std::any]
         (see [ml_codomain_erases_to_any]), wrap the result with
         [std::any_cast<T>] to recover the caller's concrete return type. *)
      | Some fld ->
        let declared =
          try Some (List.nth non_erased_field_types (n - i)) with _ -> None
        in
        (* An instance keeps a method's own quantifier -- a higher-kinded
           class's every method, and any method parametric in a type of its
           own ([mapf : forall A, (A -> A) -> A -> A]): the method is a member
           template, not a signature erased at [std::any], so neither its
           arguments nor its result are erased here.  The count is the one the
           instance and the concept read ({!Ml_type_util.method_tvar_count}). *)
        let member_template =
          match typ, declared with
          | Miniml.Tglob (r, _, _), _ when Table.get_ind_hkt_params r <> [] -> true
          | Miniml.Tglob (r, _, _), Some d ->
            method_tvar_count r (recover_method_quantifier r fld d) > 0
          | _ -> false
        in
        let fld_ty_opt =
          if not member_template then declared
          else
            (* The class's [ip_types] entry has already erased the method's own
               [forall A]; the projection constant has not. *)
            try Some (strip_erased_method_prefix (Table.find_type fld))
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
            (* The projection is inlined generically -- the [MLcase]'s own
               annotation still says [C A] -- so the instance's arguments come
               off the receiver, which names a concrete instance. *)
            let from_receiver =
              match t with
              | MLglob (r, _) | MLmagic (_, MLglob (r, _)) -> (
                match resolve_tmeta (Table.find_type r) with
                | Miniml.Tglob (_, (_ :: _ as args), _) -> Some args
                | _ | (exception Not_found) -> None )
              | _ -> None
            in
            match from_receiver with
            | Some args -> args
            | None -> (
              match typ with Miniml.Tglob (_, args, _) -> args | _ -> [] )
          in
          let n_class_params = List.length class_args in
          (* A class parameter the instance fixed at a type extraction erased
             entirely is [std::any] on the instance side (see
             {!Ml_type_util.instance_type_args}); the call has to agree, or it
             passes the wrong number of arguments. *)
          let erased_class_param j =
            match List.nth_opt class_args (j - 1) with
            | Some t -> isTdummy t
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
            match resolve_tmeta ty with
            | _ when member_template -> ty
            | Miniml.Tvar (_, j) when j > n_class_params || erased_class_param j
              ->
              Miniml.Tunknown
            | Miniml.Tvar (_, j) as ty -> (
              match List.nth_opt class_args (j - 1) with
              | Some arg -> arg
              | None -> ty )
            | Miniml.Tarr (a, b) ->
              Miniml.Tarr (at_instance_args a, at_instance_args b)
            | Miniml.Tglob (g, l, a) ->
              Miniml.Tglob (g, List.map at_instance_args l, a)
            | t -> t
          in
          match fld_ty_opt with
          | Some ft ->
            List.filter_map
              (fun t ->
                if isTdummy t || Table.is_typeclass_type t then None
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
          let is_erased = function MLdummy _ -> true | _ -> false in
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
              (fun i a -> not (is_erased a) || not (isTdummy (List.nth doms i)))
              args
        in
        (* A class-typed argument is not a value: the concept is met by a type,
           and the method declares it as a template parameter.  It leaves the
           argument list for the callee's explicit template arguments, which is
           the only place that parameter can be given. *)
        let tc_args, _, value_args =
          (* The arguments stand under the branch's binders, as [arg_exprs]
             below generates them. *)
          split_instance_args env' value_args
        in
        let call =
          (* The arguments live under the branch's binders, so the ML type
             environment must be pushed alongside [env'] for the erasure
             checks below to see their real types. *)
          let saved_env_types = (!tctx).env_types in
          let saved_erased = save_erased_env () in
          push_binders env branch_binders;
          (* Source order, as {!mk_arity_call} takes them.  Under the
             branch's binders the move-tracking indices are too: unshifted, an
             argument's index names whatever outer variable sits that many
             binders further out -- the borrowed field [ta] read as the owned
             local [k], and moved out of the node it shares. *)
          let arg_exprs =
            with_shifted_move_tracking (List.length branch_binders) @@ fun () ->
            List.mapi
              (fun j a ->
                let e =
                  match a with
                  | MLdummy _ -> Cpp_erasure.empty_box
                  | _ -> gen_expr ~slot env' a
                in
                match List.nth_opt fld_param_tys j with
                | Some (Miniml.Tapp _ as pt) when not is_typeclass ->
                  (* The dictionary's method is stored monomorphically, over
                     the carrier at the erased element, and a carrier does not
                     convert elementwise on its own -- [optional<any>] built
                     from an [optional<Nat>] holds the {e optional}, not the
                     [Nat].  Box the elements on the way in, as the result is
                     unboxed on the way out. *)
                  CPPcontainer_cast (cpp_of_ml env' pt, e, false)
                | Some pt -> erase_fn_arg_for_param env' pt a e
                | None -> e )
              value_args
          in
          restore_env_types saved_env_types;
          restore_erased_env saved_erased;
          let callee =
            if not member_template then make_field_access (gen_expr env t) fld
            else
              (* The instance's method is a member template (its own [forall A]
                 survives), and its type parameters are not always deducible --
                 [mret : A -> M A] mentions [A] only in its result -- so they
                 are passed explicitly. *)
              let ipv =
                match typ with
                | Miniml.Tglob (r, _, _) ->
                  List.length (Table.get_ind_ip_vars r)
                | _ -> 0
              in
              let nmax =
                match fld_ty_opt with
                | Some ft -> Mlutil.type_maxvar ft
                | None -> 0
              in
              if nmax <= ipv then make_field_access (gen_expr env t) fld
              else
                let tvars = get_current_type_vars () in
                let targs =
                  List.init (nmax - ipv) (fun k ->
                      convert_ml_type_to_cpp_type env tvars
                        (Miniml.Tvar (Schematic, (ipv + 1 + k))) )
                in
                CPPscope ( gen_expr env t,
                    Common.id_of_global Term fld,
                    targs )
          in
          (* The class-typed arguments follow the method's own type variables,
             which is the order the instance declares them in. *)
          let callee =
            match (tc_args, callee) with
            | [], _ -> callee
            | _, CPPscope (b, id, tys) ->
              CPPscope
                (b, id, tys @ List.filter_map (ml_arg_to_template_type env') tc_args)
            | _ -> callee
          in
          (* A class method is a static member function of the instance
             struct, so its arity is the field's. *)
          mk_arity_call
            ?params:
              (Option.map
                 (fun _ -> List.map (cpp_of_ml env') fld_param_tys)
                 fld_ty_opt )
            ~saturated:(mk_call callee)
            arg_exprs
        in
        let n_value_args = List.length value_args in
        let erased_cod =
          match fld_ty_opt with
          | Some ft -> (not member_template) && ml_codomain_erases_to_any n_value_args ft
          | None -> false
        in
        let call = recover_boxed_result ~boxed:erased_cod ~expected:expected_ty call in
        recover_carrier_result
          ~fun_ty:(if is_typeclass then None else fld_ty_opt)
          ~n_args:n_value_args ~want:expected_ty call
      | _ -> CErrors.anomaly (Pp.str "record field index out of bounds") )
    | _ ->
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
             (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
             ids )
          env
      in
      (* renamed_ids is in reversed order (from List.rev_map above). Reverse it
         back so it aligns with ids (constructor / field order). *)
      let renamed_ids_fwd = List.rev renamed_ids in
      let asgns =
        List.concat_map
          (fun (i, ((renamed_name, _), (_, ty))) ->
            let fld =
              try Some (List.nth non_erased_fields i) with _ -> None
            in
            let e =
              match fld with
              | Some fld -> make_field_access (gen_expr env t) fld
              | _ -> CErrors.anomaly (Pp.str "record field index out of bounds")
            in
            let e =
              match typ with
              | Tglob (record_ref, _, _) ->
                let storage_ty =
                  convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton record_ref)
                    []
                    ty
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env [] ty
                in
                wrap_api_expr ~storage_ty ~api_ty e
              | _ -> e
            in
            let decl_ty =
              convert_ml_type_to_cpp_type env [] ty
            in
            match lift_iife_assignment renamed_name (Some decl_ty) e with
            | Some stmts -> stmts
            | None -> [Sasgn (renamed_name, Declare decl_ty, e)])
          (List.mapi (fun i x -> (i, x)) (List.combine renamed_ids_fwd ids))
      in
      mk_iife None
        (asgns
         @ with_iife_return_type expected_ty (fun () ->
               gen_stmts ~slot env' (fun x -> Sreturn (Some x)) body)) )
    (* Known limitation: simultaneous pattern matching on record fields is not
       supported — each field is destructured individually. *)
  | MLcase (typ, t, pv) when lang () == Cpp ->
    gen_cpp_case typ t env pv
  | MLletin (_, ty, _, _) as a ->
    with_escape_analysis (fun () ->
      with_iife_return_type expected_ty (fun () ->
        mk_iife None (gen_stmts env (fun x -> Sreturn (Some x)) a) ) )
  | MLfix _ as a ->
    (* Bare fixpoint in expression context — wrap in IIFE, delegate to
       gen_stmts. *)
    with_escape_analysis (fun () ->
      mk_iife None (gen_stmts env (fun x -> Sreturn (Some x)) a) )
  | MLstring s -> CPPstring s
  | MLuint x -> CPPuint x
  | MLfloat f -> CPPfloat f
  | MLparray (elems, def) ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    CPPparray (elems, def)
  | MLmagic (m, t) ->
    (* A value crossing into a slot that is really [std::any] has to be built
       at the canonical erased shape -- every component boxed -- because the
       consumer recovers it with a fixed [any_cast] and cannot know the
       concrete component types.  Extraction recorded both sides of this
       boundary, so ask for that shape whenever [into] is the erased one and
       [from] is not.  See [deep_erase] on {!gen_expr}. *)
    let into_is_erased_only =
      match m with
      | Mcoerce (from, into) ->
        (* The destination this value is actually being built into outranks
           the coercion's inferred target: a call site that names a concrete
           parameter type -- an instance's associated type, say -- has pinned
           the slot down, while the recorded [into] is a type variable this
           scope cannot resolve and so reads as erased. *)
        (match expected_ty with
            | Some t -> prints_as_any t
            | None -> true)
        && prints_as_any (cpp_of_ml env into)
        && not (prints_as_any (cpp_of_ml env from))
      | Mboxed | Mbarrier -> false
    in
    (* A lambda is written against the slot it fills -- its binders and
       arity are the slot's -- and a coercion cannot reshape a callable after
       the fact. *)
    let inner =
      gen_expr
        ?expected_ty:(match t with MLlam _ -> expected_ty | _ -> None)
        ~slot:{slot with deep_erase = slot.deep_erase || into_is_erased_only} env t
    in
    (* What extraction recorded about the term's own side of the boundary.
       Not materialised: this is an inferred type, so a [Topaque] here stays
       [Topaque] and licenses nothing. *)
    let recorded_from =
      match m with
      (* A binder whose C++ type is decided outranks the coercion's recorded
         source, for the reason given for [Mboxed] below: [md] destructured out
         of a typed pattern is a [List<metadata<std::any>>], whatever erased
         carrier application the coercion recorded for it. *)
      | Mcoerce (from, _) -> (
        match t with
        | MLrel i -> (
          match binder_cpp_type i with
          | Some ty when not (prints_as_any ty) -> Some ty
          | _ -> Some (cpp_of_ml env from) )
        | _ -> Some (cpp_of_ml env from) )
      (* [Mboxed] is extraction's reading of the Coq typing.  A binder whose
         C++ type was decided at its binding site outranks it: a type-class
         method returning [M A] is opaque in Coq, but Crane emits the
         instance's [M] as a template, so the value here has the concrete type
         the binder was assigned and there is no box to open. *)
      | Mboxed -> (
        match t with
        | MLrel i -> ( match binder_cpp_type i with
          | Some ty -> Some ty
          | None -> Some Tany )
        | _ -> Some Tany )
      | Mbarrier -> None
    in
    ( match expected_ty with
      | Some ty when not (prints_as_any ty) && ty <> Tvoid
                    && not (match ty with Tglob (g, _, _) -> Table.is_erased_type_const g | _ -> false) ->
        let rec is_cpp_erased_var_rec = function
          | MLrel i -> binder_is_boxed i
          | MLmagic (_, t') -> is_cpp_erased_var_rec t'
          | _ -> false
        in
        let is_cpp_erased_var = is_cpp_erased_var_rec t in
        (* Namespace-collapsing erase: a namespaced leaf like [R] must become
           plain [std::any], not the malformed [typename R::std::any] the shared
           [erase_type_to_any] produces for a [Tnamespace]-wrapped [Tglob].
           This unwraps the erased var to its runtime representation
           ([deque<std::any>] for a custom list of [R]); a downstream consumer
           that needs the CONCRETE element container (e.g. a constructor field
           of type [deque<R>]) converts it with [crane_container_cast] at its
           own site (mirroring [eta_fun]'s function-argument path). *)
        if is_cpp_erased_var then
          (* Canonical erased shape is [deque<std::any>] (a bare [std::any]
             per element, not a structure-preserving [pair<any,any>]) -- see
             the matching fix in the [MLrel] case above. *)
          let erase_top_args = function
            | Tglob (g, args, ns) when args <> [] ->
              Tglob (g, List.map (fun _ -> Tany) args, ns)
            | Tnamespace (ns_g, Tglob (g, args, ns)) when args <> [] ->
              Tnamespace (ns_g, Tglob (g, List.map (fun _ -> Tany) args, ns))
            | t -> t
          in
          coerce ~from:Tany ~into:(erase_top_args ty) inner
        else if ml_expr_is_erased env t then
          (* Extraction's oracle reads a type-class method's [M A] as erased,
             but the binder it is bound to was assigned {!Minicpp.Topaque} --
             an admission that the shape could not be resolved, not a box.
             Say so rather than assert [Tany]: {!coerce} recovers from a box
             and must not invent one. *)
          let rec binder_is_opaque = function
            | MLrel i -> binder_cpp_type i = Some Topaque
            | MLmagic (_, t') -> binder_is_opaque t'
            | _ -> false
          in
          coerce ~from:(if binder_is_opaque t then Topaque else Tany)
            ~into:ty inner
        else
          (* [ml_expr_is_erased] only recognises a handful of shapes and says
             [false] for the rest.  Extraction already unified the two sides
             here, so fall back on what it recorded rather than on the
             oracle's silence. *)
          ( match recorded_from with
            (* Only the boxed dimension: extraction's [from] describes the
               Coq-level type, and the pointer- and converting-constructor
               dimensions at this boundary have already been settled by the
               sub-expression that produced [inner]. *)
            (* Unless the value is a component just read out of an erased
               pair and the type the context has in mind is itself a pair:
               that read already handed back the component's own box, so the
               context's type describes the enclosing pair, not the component,
               and recovering here would name the wrong one.  When the context
               wants a non-pair, it is talking about the component, and the
               box does have to be opened. *)
            | Some from
              when prints_as_any from
                   && not
                        ( is_erased_pair_component inner
                        &&
                        match ty with
                        | Tglob (g, _, _) -> is_prod_global g
                        | _ -> false ) ->
              coerce ~from ~into:(boxed_shape_of ty) inner
            | Some _
              when ( match m with
                   | Mcoerce (from, _) -> absurd_coercion from ty
                   | Mboxed | Mbarrier -> false ) -> (
              match m with
              (* Absurd only at some instantiations: [tt] read at the index [T1]
                 of [Inc : incE unit] is dead unless [T1] is [unit] -- or the
                 box an erased handler instantiates it at.  Which, C++ decides
                 once it substitutes [T1]. *)
              | Mcoerce (from, _) when contains_tvar ty ->
                mk_iife (Some ty)
                  [ Sif_constexpr
                      ( Tt_convertible (ty, Tref (Lvalue, Tconst (cpp_of_ml env from))),
                        [Sreturn (Some (CPPconvert (ty, inner)))],
                        [Sthrow Minicpp.dead_branch_message] ) ]
              | _ -> CPPabort (Minicpp.dead_branch_message, ty) )
            | _ -> inner )
      | _ -> inner )
  | MLdummy _ ->
    (* Erased proof or type argument.  [CPPabort] is safe here because this
       case only fires in dead code positions (absurd match branches).
       Evaluated positions — constructor args and custom-constructor args —
       are handled before reaching this point: see [gen_ctor_arg] in the
       [MLcons] case and in {!gen_expr_custom_cons}, which produce
       [std::any{}] instead.  The reuse optimization in {!gen_cpp_case}
       skips [MLdummy] fields entirely. *)
    CPPabort ("unreachable", abort_ty expected_ty)
  | MLexn msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    CPPabort (msg, abort_ty expected_ty)
  | MLaxiom s -> CPPabort ("unrealized axiom: " ^ s, abort_ty expected_ty)
  | _ -> CErrors.anomaly (Pp.str "gen_expr: unhandled ML AST node")

(* Call class field [x] as a static member of the instance struct [inst].

   Rocq hands a projection over already applied where the instance is
   concrete, so the term is an ordinary application and not the single-branch
   match a projection through an instance {e variable} extracts to; the C++ is
   the same either way. *)
and project_through_instance env x tys args inst =
  let operands =
    List.filter
      (fun a ->
        match a with
        | MLdummy _ -> false
        | _ -> not (is_typeclass_instance_arg env a) )
      args
  in
  (* The instance declares each method as a member template over the method's
     own type variables -- the class's parameters are the instance, not
     parameters of its methods -- so the call's type arguments minus the
     class's are the method's.  The class's stand in front of the dictionary
     in the projection's type, erased.  They are given explicitly rather than
     deduced: a method declares its continuation as a [std::function], which
     a closure does not deduce, and [ret] mentions its variable only in its
     result. *)
  let targs =
    let n_class = Ml_type_util.projection_class_arity x in
    List.map (cpp_of_ml env) (List.filteri (fun i _ -> i >= n_class) tys)
  in
  (* What each operand is written into.  [tys] leads with the carrier, which
     is how the field's own type numbers the class parameter, so the single
     substitution that instantiates the method also resolves [m A] -- and
     without it an operand that spells its type for the first time, a match
     whose branches have to agree on one return type, is built at whatever
     the enclosing declaration returns.  An argument is not a tail position,
     so that is never the right answer; see {!position_cpp_ty}.

     Only a suffix as long as the operand list is safe to read. *)
  let operand_ml_tys =
    let doms = projection_value_domains env x tys inst in
    let extra = List.length doms - List.length operands in
    if extra >= 0 then List.filteri (fun i _ -> i >= extra) doms else []
  in
  (* The instance is a type: an applied one -- [TFunctor_option
     TFunctor_box] -- is spelled as the template argument it would be. *)
  let inst_expr =
    match ml_arg_to_template_type env inst with
    | Some t -> CPPtype_name t
    | None -> gen_expr env inst
  in
  mk_call
    (CPPscope (inst_expr, Common.id_of_global Term x, targs))
    (List.mapi
       (fun i a ->
         let expected = param_expected_cpp_ty env operand_ml_tys i in
         let slot =
           {empty_slot with expected_ml_ty = List.nth_opt operand_ml_tys i}
         in
         with_cpp_return_type expected (fun () ->
             gen_expr ?expected_ty:expected ~slot env a ) )
       operands )

(** [gen_call_args ~slot ?expected_ty env plan] -- the C++ arguments of the
    call [plan] describes, each generated against the parameter it is passed
    at.  The dictionaries' promoted variables are in scope for them. *)
and gen_call_args ~slot ?expected_ty env id plan =
  let {
    cp_regular_args = regular_ml_args;
    cp_leading_params = leading_params;
    cp_expected_result = expected_result;
    cp_instance_families = instance_families;
    cp_fn_ml_ty = fn_ml_ty;
    cp_tys = tys;
    cp_dictionary_filled = dictionary_filled;
    cp_params = fn_param_ml_tys;
    cp_params_orig = fn_param_ml_tys_orig;
    cp_subst_index_of_orig = subst_index_of_orig;
    cp_tvars = tvars;
    cp_concrete_tvar_type = concrete_tvar_type;
    cp_result_tvar_map = result_tvar_map;
    _
  } = plan in
  List.mapi (fun i ml_arg ->
    match strip_magic ml_arg with
    | MLdummy _ -> (
      (* An erased value, boxed.  At a function-typed parameter it is an
         erased function -- [bif : obj -> obj -> obj] is [sum1] once [obj]
         is [Type -> Type] -- which is called, so it is a callable of the
         declared arity handing back a box. *)
      match
        Param_pos.nth fn_param_ml_tys_orig
          (Param_pos.of_regular ~leading:leading_params i)
      with
      | Some pt when count_ml_value_arrows pt > 0 ->
        mk_lambda
          (List.init (count_ml_value_arrows pt) (fun _ ->
               (Tref (Lvalue, Tconst Tauto), None) ))
          None
          [Sreturn (Some Cpp_erasure.empty_box)]
          ~capture:Closure
      | _ -> Cpp_erasure.empty_box )
    | _ ->
    (* The callee's parameters are indexed from its class-dictionary
       arguments, which [regular_ml_args] does not include, so this
       argument's parameter is at [param_index] of the unsubstituted list --
       and, being a position of that list, has to be converted before it
       indexes the substituted one (see [subst_index_of_orig]). *)
    let param_index = Param_pos.of_regular ~leading:leading_params i in
    (* Where that parameter stands in the substituted list.  The
       conversion is a statement about the callee's ML type, and it is worth
       making only where the ML type is what the callee's C++ signature was
       built from.

       For a callee whose C++ form is written out by hand it is not: the
       replacement text is what says how the arguments are taken, and it
       need not take them at the Rocq types.  [crane_itree.h] invokes
       [itree_vis]'s continuation at [std::any] whatever its Rocq domain
       [X] is, so the substituted domain ([std::monostate]) is the one type
       the lambda will never be called at -- while [itree_bind]'s, two lines
       away in the same header, is taken at exactly its Rocq domain.
       Nothing here can tell those apart, so such a callee keeps reading the
       position it always read: no better answer is available, and a
       confident wrong one is worse than the familiar one. *)
    let subst_param_index =
      if Table.is_inline_custom id then
        Some (Param_pos.subst_at_declared param_index)
      else subst_index_of_orig param_index
    in
    (* Where substitution erased the parameter -- [IFun b c] at objects the
       call erases -- the declaration still takes it, at the type it
       declares, and an argument reaching it is recovered at that type. *)
    let param_ml_ty =
      match subst_param_index with
      | Some i -> Param_pos.nth fn_param_ml_tys i
      | None -> (
        match Param_pos.nth fn_param_ml_tys_orig param_index with
        | Some t when not (Mlutil.isTdummy t) -> Some t
        | _ -> None )
    in
    (* {b Lambda arity limiting.}  When a lambda argument has more binders
       than the callee's parameter type has top-level arrows, the extra
       binders come from the return type being a function (instantiated
       from a type variable).  For example, [fold_right]'s callback type
       is [B -> A -> A]; when [A = nat -> nat], the lambda
       [fun t acc => fun x => body] has 3 binders but the parameter has
       only 2 arrows.  Flattening all 3 into a single C++ lambda produces
       a 3-arg function, which doesn't match the 2-arg is_invocable_v constraint.

       Fix: insert an [MLmagic] barrier after the expected number of
       binders so that [collect_lams] in [gen_expr] stops there.  The
       inner binders become a returned inner lambda.  We use the
       {i non-substituted} parameter type to count arrows, because type
       variable substitution would inflate the count (e.g. [Tvar A]
       becoming [Tarr(nat, nat)] adds a spurious arrow).

       Additionally, annotate the outer lambda with an explicit return
       type derived from the {i substituted} parameter type's codomain.
       Without this, the deduced return type is the inner lambda's
       unique closure type, and [is_invocable_r_v<std::function<...>,
       closure_type>] may evaluate to [false] in concept checking
       (C++ lambda-to-[std::function] conversion is not recognized
       during SFINAE in some implementations). *)
    let ml_arg, split_ret_ty =
      match ml_arg with
      | MLlam _ ->
        ( match Param_pos.nth fn_param_ml_tys_orig param_index with
        | Some param_ty ->
          let rec count_arrows = function
            | Miniml.Tarr (_, rest) -> 1 + count_arrows rest
            | _ -> 0
          in
          let expected = count_arrows param_ty in
          let actual = Mlutil.nb_lams ml_arg in
          if expected > 0 && actual > expected then
            let outer_ids, inner_body =
              Mlutil.collect_n_lams expected ml_arg
            in
            let barrier =
              Mlutil.named_lams outer_ids (MLmagic (Mbarrier, inner_body))
            in
            (* Compute the return type from the substituted param type by
               stripping [expected] top-level arrows.  The remaining type
               is the function-typed codomain that the inner lambda
               implements.

               When the substituted codomain is still a [Tvar] (happens
               when [tys = []] so substitution is a no-op), use the
               [concrete_tvar_type] computed above — it holds the
               concrete [T1] type derived from the excess args and the
               enclosing function's return type. *)
            let ret_ty =
              match param_ml_ty with
              | Some subst_pt ->
                let rec codomain_after n = function
                  | Miniml.Tarr (_, rest) when n > 0 ->
                    codomain_after (n - 1) rest
                  | ty -> ty
                in
                let ret_ml = codomain_after expected subst_pt in
                ( match resolve_tmeta ret_ml with
                | Miniml.Tvar (_, _) -> concrete_tvar_type
                | _ ->
                  Some (cpp_of_ml env ret_ml) )
              | None -> None
            in
            (barrier, ret_ty)
          else
            (ml_arg, None)
        | None -> (ml_arg, None) )
      | _ -> (ml_arg, None)
    in
    let param_expected_at params pos =
      match Param_pos.nth params pos with
      | Some ml_ty ->
        let cpp_ty = cpp_of_ml env ml_ty in
        if prints_as_any cpp_ty then None else Some cpp_ty
      | None -> None
    in
    (* The concrete types come from the substituted parameter type, but its
       {e arity} must come from the unsubstituted one: substituting a
       function type into a codomain that was a type variable flattens the
       element's arrows into the callable's own parameter list, and a
       template argument keeps its currying (see
       {!template_arg_of_ml_type}).  A parameter declared as a bare type
       variable has arity zero, so its value is curried throughout. *)
    (* This parameter's substituted C++ type.  [param_index] counts
       positions of the unsubstituted type, so it has to be converted before
       it indexes the substituted list -- see [subst_index_of_orig]. *)
    let param_expected_subst () =
      Option.bind subst_param_index (param_expected_at fn_param_ml_tys)
    in
    (* Just the re-currying: [None] where the declaration's arity is already
       the shape the substituted parameter type has, so a producer that has
       its own better source keeps it. *)
    let param_expected_recurried () =
      match Param_pos.nth fn_param_ml_tys_orig param_index with
      | Some orig ->
        Option.bind (param_expected_subst ())
          (recurry_to_opt (count_ml_value_arrows orig))
      | None -> None
    in
    let param_expected_at_declared_arity () =
      match param_expected_recurried () with
      | Some _ as t -> t
      | None -> (
        match Param_pos.nth fn_param_ml_tys_orig param_index with
        | Some _ -> param_expected_subst ()
        | None -> None )
    in
    (* The callee declares this parameter as one of its own template
       parameters [Tvar j], and some {e other} parameter carries that same
       [j] in a position the instantiation erased -- so that parameter's
       argument deduces [j] as [std::any].  This one has to arrive boxed for
       the two deductions to agree.  Erasure of the type argument alone is
       not enough of a reason: unless another position states it as
       [std::any], boxing here would be the only thing making the deduction
       disagree. *)
    let param_tvar_erased =
      let this = param_index in
      let rec mentions j = function
        | Miniml.Tvar (_, j') -> j = j'
        | Miniml.Tglob (_, ts, _) -> List.exists (mentions j) ts
        | Miniml.Tapp (h, ts) -> h = j || List.exists (mentions j) ts
        | Miniml.Tarr (a, b) -> mentions j a || mentions j b
        | Miniml.Tmeta {contents = Some t} -> mentions j t
        | _ -> false
      in
      let tvar_arg_erased j =
        match List.nth_opt tys (j - 1) with
        | Some t ->
          Ml_type_util.has_erased_type_in_type
            (unfold_cpp_typedef env (cpp_of_ml env t))
        | None -> false
      in
      match Param_pos.nth fn_param_ml_tys_orig this with
      | Some (Miniml.Tvar (_, j)) when tvar_arg_erased j ->
        List.exists
          (fun (k, orig) ->
            (not (Param_pos.equal k this))
            && param_states_type_args id orig
            && mentions j orig
            && Ml_type_util.has_erased_type_in_type
                 (unfold_cpp_typedef env (cpp_of_ml env (type_subst_list tys orig))))
          (Param_pos.positioned fn_param_ml_tys_orig)
      | _ -> false
    in
    let arg_expected_ty =
      match ml_arg with
      (* A lambda under a coercion is written against the slot all the
         same. *)
      | MLlam _ | MLmagic (_, MLlam _) -> param_expected_at_declared_arity ()
      | _ ->
      ( match
          match Param_pos.nth fn_param_ml_tys_orig param_index with
          | Some (Miniml.Tvar (_, _)) ->
            param_expected_at_declared_arity ()
          | _ -> None
        with
      | Some _ as t -> t
      | None ->
      ( match ml_arg with
      | MLmagic (_, _) -> param_expected_subst ()
      (* [MLglob]: a bare function name handed over as a value may need
         re-currying.  Count the arrows in the callee's {e unsubstituted}
         parameter type: arrows past the point where the codomain becomes a
         type variable belong to the element type the callee is generic in,
         not to the callable it expects. *)
      | MLglob _ -> param_expected_at fn_param_ml_tys_orig param_index
      (* A partial application is a callable built here rather than named,
         and reaches the slot at the arity the callee declared the parameter
         at, for the same reason a lambda does. *)
      | MLapp _ -> param_expected_at_declared_arity ()
      (* A constructed value is spelled here for the first time, so only the
         slot can say how its type arguments are curried.  Everything else
         about the type the constructor's own annotation knows better: it
         carries this producer's instantiation, which the parameter type may
         have erased.  So take the currying and nothing else. *)
      | MLcons _ -> param_expected_recurried ()
      (* A match in argument position becomes an immediately-invoked lambda,
         whose branches have to agree on one return type -- and the branches
         are where a value is spelled for the first time, so nothing inside
         states it.  Only the slot does. *)
      | MLcase _ -> param_expected_at_declared_arity ()
      | _ -> None ) )
    in
    (* Where the substituted parameter says nothing, the result may:
       [trigger (subevent ...)] at a tree of family [Sum1<...>] fixes
       [trigger]'s family, which is what its parameter -- the [subevent]
       call's result -- has to be. *)
    let arg_expected_ty =
      match
        ( Lazy.force result_tvar_map,
          Param_pos.nth fn_param_ml_tys_orig param_index )
      with
      | (result_names, (_ :: _ as m)), Some pt -> (
        let d =
          convert_ml_type_to_cpp_type env result_names (type_simpl pt)
          |> deapply_families
          |> map_cpp_type (function
               | Tvar (Tv_index (_, Some v) | Tv_named v) as t -> (
                 match List.find_opt (fun (v', _) -> Id.equal v v') m with
                 | Some (_, t') -> t'
                 | None -> t )
               | t -> t )
        in
        match arg_expected_ty with
        (* No slot at all: the declaration's type is the slot, where it is
           one this scope can write. *)
        | None | Some Tany ->
          ( match spell_in_scope d with
          | Some _ as t -> t
          | None -> arg_expected_ty )
        (* A slot erased inside: each erased part is filled from the
           declaration where it says; what the declaration still says in
           its own variables is no answer. *)
        | Some slot ->
          let scope = current_scope_type_names () in
          let d =
            map_cpp_type
              (function
                | Tvar tv as t ->
                  let id = tvar_spelled tv in
                  if List.exists (Id.equal id) scope then t else Tany
                | t -> t )
              d
          in
          Some (Ml_type_util.refine_erased_by ~expected:d slot) )
      | _ -> arg_expected_ty
    in
    (* Only a parameter the carrier reaches: one that mentions a
       higher-kinded variable of the callee.  [interp_state]'s tree
       [itree E T] is at the source family [E], and filling its erased
       family with the monad's [BotE] turned the inner [interp] into one
       over the target family. *)
    let param_mentions_carrier =
      match Param_pos.nth fn_param_ml_tys_orig param_index with
      | Some t ->
        let hk = declared_higher_kinded_tvars fn_ml_ty in
        not (IntSet.is_empty (IntSet.inter hk (collect_tvars_set IntSet.empty t)))
      | None -> true
    in
    let arg_expected_ty =
      if not param_mentions_carrier then arg_expected_ty
      else
        List.fold_left
          (fun t b -> Option.map (refine_by_instance_family b) t)
          arg_expected_ty instance_families
    in
    let arg_expected_ml_ty =
      match param_ml_ty with
      | Some ml_ty when not (ml_type_contains_erased ml_ty) -> Some ml_ty
      | _ -> slot.expected_ml_ty
    in
    (* When the callee's declared parameter type is value-dependent and
       resolves to [std::any] (e.g. [syms_semty xs]), a concrete pair/tuple
       literal passed at this call site (e.g. [(n, (n, tt))] for a literal
       [xs]) must be DEEP-erased — every component boxed into [std::any] —
       so that the callee's generic body, which reconstructs the value via
       [any_cast<pair<any,any>>], can recover it.  The deep-erasing
       constructor path in [gen_expr_custom_cons] is normally driven by the
       enclosing function's erased return type, so it is reached here by
       treating this call argument as if it were itself in erased "return"
       position for the duration of its generation. *)
    (* Where the call writes the variable -- the dictionary stated it --
       nothing deduces it, and an argument boxed to agree with a deduction
       would only fail to convert. *)
    let param_written_by_call = param_tvar_erased && dictionary_filled in
    let param_resolves_to_any =
      (param_tvar_erased && not param_written_by_call)
      ||
      match param_ml_ty with
      | Some ml_ty -> ml_erases_to_box env ml_ty
      | None -> false
    in
    let expr =
      let ret =
        if param_resolves_to_any then Some Tany
        (* An argument is not a tail position, so the enclosing function's
           return type does not describe it -- and what the parameter says
           does.  Left to {!position_cpp_ty}'s fallback, a match in argument
           position builds its branches at the type the {e call} returns.

           Only where the parameter's type can be written, though: installed
           as a return type it is written out, as the argument's own explicit
           template arguments among other places, and a type naming a skipped
           global renders there as a bare argument list -- [<std::any,
           <std::any, std::any>>].  Where it cannot be written the enclosing
           return type is not right, but it is spellable, and a parameter
           that answers in text no compiler takes has not answered. *)
        else
          match arg_expected_ty with
          | Some t when Ml_type_util.has_no_cpp_spelling t ->
            (!tctx).current_cpp_return_type
          | t -> t
      in
      with_cpp_return_type ret (fun () ->
          gen_expr ?expected_ty:arg_expected_ty
            ~slot:
              { slot with
                expected_ml_ty = arg_expected_ml_ty;
                call_result = expected_result;
                stated_ml_ty = param_ml_ty }
            env ml_arg )
    in
    (* Annotate the outer lambda with the explicit return type computed
       during the split, so that C++ concept checking sees the concrete
       [std::function<...>] return type instead of the raw closure type. *)
    let expr =
      match split_ret_ty, expr with
      | Some ret_ty, CPPlambda ({ cl_ret = None; _ } as l) ->
        CPPlambda { l with cl_ret = Some ret_ty }
      | _ -> expr
    in
    let expr =
      match (param_ml_ty, expr) with
      | Some param_ty, CPPlambda ({ cl_body = body; _ } as l) ->
        let param_cpp_ty =
          cpp_of_ml env param_ty
        in
        ( match param_cpp_ty with
        | Tfun (_, Tshared_ptr inner) ->
          let rec wrap_stmt = function
            | Sreturn (Some e) ->
              Sreturn (Some (mk_call (CPPalloc (Alloc_heap, inner)) [e]))
            | s -> map_stmt Fun.id wrap_stmt Fun.id s
          in
          CPPlambda
            { l with
              cl_ret = Some (Tshared_ptr inner);
              cl_body = List.map wrap_stmt body }
        | _ -> expr )
      | _ -> expr
    in
    let expr =
      match param_ml_ty with
      | Some param_ty -> erase_fn_arg_for_param env param_ty ml_arg expr
      | None -> expr
    in
    (* A methodified callee is spelled [recv.f(rest)], and [std::any] has no
       members: unlike every other argument, the receiver cannot arrive as a
       box at all.  What says that it does is the declaration the receiver
       came out of -- a method registered as returning [std::any] -- and the
       parameter's type is what says what the box holds. *)
    let expr =
      let receiver_is_boxed =
        (* The receiver's own ML type has to say it is gone -- a projection
           out of a dependent pair is a bare type variable, and extraction
           leaves a [Tdummy] behind. *)
        ( match
            Option.map (fun t -> cpp_of_ml env t)
              (infer_ml_body_type (strip_magic ml_arg))
          with
        | Some t -> prints_as_any t
        | None -> false )
        &&
        (* And it has to have come out of an accessor on a value that
           carries erasure: a [SigT<std::any, std::any>] hands back a box, a
           [SigT<List<uint64_t>, List<uint64_t>>] hands back a list.  A call
           whose arguments are all concrete does not qualify however its ML
           type reads -- a free template function's result is resolved by
           the type arguments the call site states. *)
        match strip_magic ml_arg with
        | MLapp (g, rargs) -> (
          match strip_magic g with
          | MLglob _ -> app_reads_erased_value env rargs
          | _ -> false )
        | _ -> false
      in
      match Cpp_names.lookup_method_this_pos id with
      | Some pos
        when Param_pos.equal (Param_pos.of_receiver pos) param_index
             && receiver_is_boxed -> (
        match param_expected_subst () with
        | Some into when not (prints_as_any into) ->
          coerce ~from:Tany ~into expr
        | _ -> expr )
      | _ -> expr
    in
    let expr =
      if param_tvar_erased && not param_written_by_call then
        (* Say where the value is coming from where the binder's own type
           says: an argument that is already a box is left alone. *)
        let from =
          match ml_arg with
          | MLrel j -> binder_cpp_type_or_derive env j
          | _ -> None
        in
        coerce ~term:ml_arg ?from ~into:Tany expr
      else expr
    in
    (* Wrap void calls as values only when the expression will be used
       as a value (not in monadic parameter handler which places it in
       statement position inside a lambda). *)
    let as_value () =
      match ml_arg with
      | a when ml_value_is_void_call a ->
        (* Don't wrap eta-expanded lambdas (partial applications) — they
           are function VALUES, not void call results. *)
        ( match expr with
        | CPPlambda _ -> expr
        | _ -> wrap_void_call_as_value expr )
      | _ -> expr
    in
    (* A bare local variable known to be boxed as [std::any]
       ([binder_is_boxed]) — e.g. a leaf pulled out of an erased-pair
       destructure — passed directly to a plain global function whose
       parameter type is concrete.  Mirrors the equivalent check for
       non-global callees (~[MLrel j when Escape.IntSet.mem ...] above). *)
    let ml_arg_is_erased_rel =
      match ml_arg with
      | MLrel j | MLmagic (_, MLrel j) -> binder_is_boxed j
      | _ -> false
    in
    match param_ml_ty with
    | Some param_ty
      when ( ml_body_returns_erased_field ml_arg || ml_arg_is_erased_rel
           (* A component read out of a pair that was itself recovered from
              a box is a [std::any] whatever its ML type says, and the
              emitted expression is the evidence -- see
              {!yields_boxed_component}. *)
           || yields_boxed_component (as_value ()) )
           && not (match param_ty with
                   | Miniml.Tglob (g, _, _) -> Table.is_promoted_type_var g
                   | _ -> false)
           (* [param_ty] comes from the callee's own (call-site-substituted)
              type signature, whose [Tvar] indices are not anchored to this
              function's [tvars] scope. When conversion produces an
              unresolved [Tvar (Tv_index (_, None))] (would print as a bogus template
              parameter like "T3"), we cannot build a meaningful concrete
              cast here — skip this branch and fall back to [as_value ()]
              unchanged; a later pass (e.g. [gen_match_branch]'s field
              substitution) supplies the correct cast at its own,
              properly-scoped [tvars]. *)
           && erase_unresolved_tvars (cpp_of_ml env param_ty)
              = cpp_of_ml env param_ty ->
      let cpp_ty = cpp_of_ml env param_ty in
      ( match strip_ns_tglob cpp_ty with
      | Tglob (g, [_], _) when is_list_global g && not (Table.is_custom g) ->
        let list_any_ty =
          match cpp_ty with
          | Tnamespace (ns_g, _) -> Tnamespace (ns_g, Tglob (g, [Tany], []))
          | _ -> Tglob (g, [Tany], [])
        in
        (* [as_value ()] may already have unboxed the erased value to the
           canonical element-erased shape (the [MLrel] case of [gen_expr]
           does this for a variable bound to an erased field).  Casting
           again would re-box that concrete list into a fresh [std::any]
           only to unbox it — mirror the custom-list branch below and reuse
           the existing cast.  It may also have gone the whole way and
           recovered the concrete list already ({!coerce} does this for a
           value crossing out of a box), in which case there is nothing
           left to convert. *)
        ( match as_value () with
        | CPPconverting_ctor (t, _) as recovered when cpp_ty_eq t cpp_ty ->
          recovered
        | CPPany_cast _ as already_cast ->
          Cpp_erasure.converting_ctor cpp_ty [already_cast]
        | v ->
          Cpp_erasure.converting_ctor cpp_ty
            [Cpp_erasure.unbox list_any_ty v] )
      | Tglob (g, [_], _) when Ml_type_util.is_custom_list_global g ->
        let clean_cpp_ty = clean_self_ns cpp_ty in
        (* Custom-extracted list (e.g. [std::deque]) is boxed as [std::any]
           with fully-erased elements at runtime ([deque<pair<any,any>>]).
           Cast the inner value to that erased representation, matching what
           [gen_match_branch]'s field substitution stores. *)
        let erased_ty =
          (* Canonical erased shape is [deque<std::any>] -- a bare [std::any]
             per element, not a structure-preserving [deque<pair<any,any>>]
             (see the matching invariant in [gen_expr]'s [MLrel]/[MLmagic]
             cases).  Using the structure-preserving erasure here would
             disagree with a sibling producer for the same Coq list type
             that already erased to the flat shape, and — when [as_value ()]
             is itself already an [any_cast] to the flat shape (added by
             [gen_expr] above) — would additionally double-wrap it in a
             second, incompatible [any_cast]. *)
          match clean_cpp_ty with
          | Tnamespace (ns_g, Tglob (g, [_], _)) ->
            Tnamespace (ns_g, Tglob (g, [Tany], []))
          | Tglob (g, [_], _) ->
            Tglob (g, [Tany], [])
          | _ -> clean_cpp_ty
        in
        let inner = match as_value () with
          | CPPany_cast _ as already_cast -> already_cast
          | v -> Cpp_erasure.unbox erased_ty v
        in
        (* When the callee is a REAL function whose parameter has a CONCRETE
           element type — a wholesale-boxed opaque element
           ([triples_le_max(const std::deque<rgb>&)]), OR a structural element
           whose concrete component must be preserved for a POLYMORPHIC/template
           callee ([nodupKeys<T1>(const std::deque<std::pair<std::string,T1>>&)],
           whose [std::string] key cannot be erased to [std::any] or template
           argument deduction fails) — the fully-erased [inner] neither converts
           nor deduces against it.  Route it through [crane_container_cast],
           which builds the concrete-element container (unboxing wholesale-boxed
           elements at runtime; for structural elements it still compiles and
           lets deduction succeed).

           Inline-custom callees (e.g. [length]'s [.size()]) splice the
           argument into a template and work on the erased container, and a
           callee whose parameter element is ALREADY fully erased
           ([deque<pair<any,any>>]) needs no conversion — both keep [inner]. *)
        let needs_concrete =
          (not (Table.is_inline_custom id))
          &&
          match strip_ns_tglob clean_cpp_ty with
          | Tglob (_, [et], _) ->
            et <> Ml_type_util.erase_type_to_any et
          | _ -> false
        in
        if needs_concrete then begin
          (* When the callee's OWN declared (unsubstituted) parameter type
             is still generic here (a template function like
             [nodupKeys<T1>]), its C++ declaration never boxes the element
             (a bare type variable never recurses).  This call site's
             [clean_cpp_ty] was built from the call-site-substituted
             concrete type though, so it may judge the (now concrete,
             possibly recursive) element as boxed — disagreeing with the
             generic declaration and breaking template argument deduction.
             Suppress boxing here to match the declaration. *)
          let callee_generic_here =
            match Param_pos.nth fn_param_ml_tys_orig param_index with
            | Some t -> Ml_type_util.ml_type_contains_tvar t
            | None -> false
          in
          CPPcontainer_cast (clean_cpp_ty, inner, callee_generic_here)
        end
        else inner
      (* The value is boxed; recover it at the parameter's type.  Going
         through {!coerce} rather than casting outright keeps the one rule
         that a destination which is itself a name for the box -- [using sel
         = std::any] -- is not a recovery target: [any_cast<sel>] reads a box
         that was never doubly wrapped and throws. *)
      | _ -> coerce ~from:Tany ~into:cpp_ty (as_value ()) )
    (* Monadic parameter (reified mode only): the callee expects
       [shared_ptr<ITree<R>>].  If the argument already produces a reified
       tree, pass through as-is; otherwise wrap in [ITree<R>::ret()]. *)
    | Some param_ty when (!tctx).itree_mode = Reified
        && is_monadic_ml_type param_ty
        && not (is_reified_monadic_expr ml_arg) ->
      Table.require_itree_header ();
      let r_ml = extract_itree_result_ml param_ty in
      let r_cpp = cpp_of_ml env r_ml in

      let itree_ty = mk_itree_type r_cpp in
      (* [expr] is a value unless the thing it calls was void-ified, in
         which case it is a statement and the tree carries [tt] instead.
         Only a genuinely valueless result gets the nullary [ret()]: a
         [unit] one has [monostate] to carry, and a tree spelled
         [ITree<void>] would not match the [ITree<Unit>] declared for it. *)
      let no_value = r_cpp = Tvoid || ml_type_is_void r_ml in
      let as_statement = no_value || ml_expr_is_void_call ml_arg in
      let ret_expr =
        if no_value then mk_itree_ret Tvoid []
        else if as_statement then mk_itree_ret r_cpp [mk_tt_expr ()]
        else mk_itree_ret_for_value r_cpp r_ml expr
      in
      let body =
        if as_statement then [Sexpr expr; Sreturn (Some ret_expr)]
        else [Sreturn (Some ret_expr)]
      in
      mk_iife (Some itree_ty) body
    (* Void-ified function reference passed as callback to polymorphic
       HOF where the ORIGINAL (non-substituted) parameter codomain is a
       type variable (not concrete unit).  The C++ definition uses a
       template type parameter constrained with is_invocable_v, so the void
       function needs wrapping to return std::monostate.  When the original
       codomain IS concrete unit, the constraint uses void which already
       accepts void-returning functions. *)
    | Some param_ty
      when (match ml_arg with
            | MLglob (r, _) | MLmagic (_, MLglob (r, _)) -> is_void_ified_ref r
            | _ -> false)
           && (match param_ty with Miniml.Tarr _ -> true | _ -> false)
           && ml_type_is_unit (ml_codomain param_ty)
           && (match Param_pos.nth fn_param_ml_tys_orig param_index with
               | Some orig_pt ->
                 not (ml_type_is_unit (ml_codomain orig_pt))
               | None -> false) ->
      let dom_mls =
        let rec collect acc = function
          | Miniml.Tarr (t, rest) ->
            ( match resolve_tmeta t with
            | Miniml.Tdummy _ -> collect acc rest
            | t -> collect (t :: acc) rest )
          | _ -> List.rev acc
        in
        collect [] param_ty
      in
      let dom_cpps =
        List.map
          (fun t -> cpp_of_ml env t)
          dom_mls
      in
      let params =
        List.mapi
          (fun j ty ->
            (Tref (Lvalue, Tconst ty), Some (Id.of_string (Printf.sprintf "_wa%d" j))))
          dom_cpps
      in
      let args =
        List.rev_map (fun (_, id) -> CPPvar (Option.get id)) params
      in
      let body =
        [ Sexpr (CPPfun_call (call_opaque, expr, of_reversed args));
          Sreturn (Some (mk_tt_expr ())) ]
      in
      mk_lambda params None body ~capture:Immediate
    | _ -> as_value ()
  ) regular_ml_args

and eta_fun ?(slot = empty_slot) ?expected_ty env f args =

  let rec get_eta_args dom args =
    match (dom, args) with
    | _ :: dom, _ :: args -> get_eta_args dom args
    | _, _ -> dom
  in
  (* Save and clear the single-use closure flag so that nested eta_fun calls
     (from processing args) do not inherit it. The saved value is used when
     this eta_fun constructs a partial-application lambda. *)
  let eta_keep_moves = slot.eta_keep_moves in
  (* Read once: the flag describes this closure, not anything built inside it. *)
  let slot = {slot with eta_keep_moves = false} in
  match f with
  | MLglob (id, tys) ->
    let plan = plan_call ~slot ?expected_ty env id tys args in
    let {
      cp_excess_args = excess_args;
      cp_primary_args = primary_ml_args;
      cp_instance_args = typeclass_ml_args;
      cp_regular_args = regular_ml_args;
      cp_leading_params = leading_params;
      cp_params_orig = fn_param_ml_tys_orig;
      cp_subst_index_of_orig = subst_index_of_orig;
      cp_tvars = tvars;
      cp_instance_promoted = instance_promoted_map;
      _
    } = plan in
    let args =
      with_promoted_var_map (instance_promoted_map @ (!tctx).promoted_var_map)
        (fun () -> gen_call_args ~slot ?expected_ty env id plan)
    in
    let ty, tys, all_type_args, written_tvar_args =
      call_type_args ?expected_ty env id plan args
    in
    let cglob = mk_cppglob ?yields:(glob_yields env id tys) id all_type_args in
    (* Check if this is a typeclass instance used as a type (for :: access).
       When all args are consumed (domain and args both empty after filtering),
       return just the type reference, not a function call. This avoids
       generating numOption<numNat, unsigned int>() instead of numOption<numNat,
       unsigned int> for qualified access like ::to_nat. *)
    let id_is_typeclass_instance = ref_returns_typeclass id in
    (* {b Curried excess args.}  When a call site provides more value args
       than the callee's ML type has arrows, the extras are curried onto the
       result: [f(primary_args)(excess_args)].

       This is valid when the callee genuinely returns a function:
       - Its codomain is a type alias ([Tglob]) that may expand to [Tarr]
         (e.g. [State S A = S -> A * S]).
       - Its codomain is a type variable ([Tvar]) that, after instantiation
         with the call-site type args [tys], becomes [Tarr] (e.g.
         [fold_right] with [B = nat -> nat]).
       - It is an inlined custom constant (e.g. [fst], [snd]).

       When the codomain is a type variable that instantiates to a
       non-function type (e.g. [div2_rect] with [T1 = R_div2]), the excess
       args come from proof-certificate functions ([Function] vernacular
       [_correct] terms) that are never called at runtime.  We emit an abort
       placeholder for those. *)
    (* The callee's instantiation at this call: the explicit type arguments
       where the site carries them, and otherwise the one its arguments
       imply. *)
    let inst_tys =
      if tys <> [] then tys
      else
        match find_type_opt id with
        | Some ml_ty -> tvar_instantiation ml_ty primary_ml_args
        | None -> []
    in
    (* The callee's codomain as this call instantiates it. *)
    let instantiated_codomain ml_ty =
      let cod = ml_codomain ml_ty in
      if inst_tys = [] then cod else Mlutil.type_subst_list inst_tys cod
    in
    let wrap_excess base =
      if excess_args = [] then
        base
      else (
        let ret_is_chainable =
          is_inline_custom id
          ||
          match find_type_opt id with
          | Some ml_ty ->
            let cod = ml_codomain ml_ty in
            ( match resolve_tmeta cod with
            | Miniml.Tglob _ -> true
            | Miniml.Tarr _ -> true
            | Miniml.Tunknown -> true
            (* A codomain that applies a variable -- [interp]'s [M R], at
               [M := stateT S m] -- is a function exactly where the variable
               is instantiated at one, which is the same question as for a
               bare variable. *)
            | Miniml.Tvar (Schematic, _) | Miniml.Tapp _ ->
              (* Type variable: instantiate with the call-site type args to
                 determine if the return type is actually a function.
                 [cod] is already the function's codomain (all arrows
                 stripped), so after substitution we check [cod_inst]
                 directly — NOT [ml_codomain cod_inst], which would strip
                 another layer of arrows and reject valid cases like
                 [fold_right] instantiated at [A = nat -> nat].

                 When [tys] is empty (type args carried as [MLdummy] in
                 [args] rather than in the [MLglob] type-arg list),
                 substitution is a no-op and the [Tvar] stays unresolved.
                 In this case, chain unconditionally: Rocq's type system
                 guarantees that excess {i value} args (non-[MLdummy]) can
                 only exist when the return type instantiates to a function.
                 Proof-level excess args are already removed by the
                 [MLdummy] filter above. *)
              if inst_tys = [] then
                true
              else
                let cod_inst = Mlutil.type_subst_list inst_tys cod in
                ( match resolve_tmeta cod_inst with
                | Miniml.Tarr _ -> true
                | Miniml.Tglob _ -> true
                | Miniml.Tdummy Miniml.Ktype -> true
                | Miniml.Tunknown -> true
                | _ -> false )
            | _ -> false )
          | None -> false
        in
        (* The callee hands back a box, so the excess args are applied to a
           [std::any] and have to go through the erased calling convention.
           A result pinned down only by a type index is written [std::any] in
           the declaration however this call site instantiates it, so it
           counts here just as it does in {!gen_expr}'s [MLapp] case. *)
        let cod_is_erased =
          match find_type_opt id with
          | Some ml_ty ->
            ml_erases_to_box env (instantiated_codomain ml_ty)
            || ( match result_cpp_via_receiver env ml_ty primary_ml_args with
               | Some c -> is_boxed_source c
               | None -> false )
            || result_is_index_only_tvar ml_ty
          | None -> false
        in
        (* The codomain as this call site instantiates it: that is the type
           the excess args are applied to. *)
        let cod_inst =
          match find_type_opt id with
          | Some ml_ty -> Some (instantiated_codomain ml_ty)
          | None -> None
        in
        (* A codomain that is a type variable takes its C++ shape from the
           template argument, which keeps its currying; one written in the
           declaration is flattened there. *)
        let cod_is_curried =
          match find_type_opt id with
          | Some ml_ty -> ml_codomain_is_tvar ml_ty
          | None -> false
        in
        (* A codomain that stays curried in C++ -- a [std::function] whose
           result is another [std::function] -- takes only the arguments of
           its own arrow, so applying every excess arg in one call would
           overrun it.  The args go in the groups the type accepts them in. *)
        (* The callee's codomain as the call writes it: its declared type at
           the written type arguments, which is what C++ returns -- [case_]'s
           [T2] written [std::function<std::any(std::any)>] where the ML
           instantiation erased the morphism type. *)
        let written_cod =
          let subst i = if i >= 1 then List.nth_opt written_tvar_args (i - 1) else None in
          match
            Option.map
              (fun t -> Minicpp.subst_cpp_tvars subst (cpp_of_ml env t))
              (find_type_opt id)
          with
          | Some (Tfun (_, c)) -> Some c
          | _ -> None
        in
        (* A group the written type returns boxed, with the rest of the chain
           still to apply: the box holds what an erased morphism produced, the
           result type at an index it never instantiated.  That is the type
           the whole chain is expected to have, as a function of the rest,
           with this declaration's own variables erased -- a handler combined
           by [case_], answering at [std::any] where the enclosing handler
           says [T1].  The chain's value is then read at the expected type. *)
        let boxed_group_target rest_ml =
          match (written_cod, expected_ty) with
          | Some (Tfun (_, c)), Some exp when prints_as_any c && not (prints_as_any exp) ->
            let arg_ty a =
              match a with
              | MLrel j -> binder_cpp_type_or_derive env j
              | _ -> Option.map (cpp_of_ml env) (ml_ast_type_hint a)
            in
            let rest_tys = List.map arg_ty rest_ml in
            if List.for_all Option.has_some rest_tys then
              let scope = get_current_type_vars () in
              let erase_own =
                map_cpp_type (function
                  | Tvar tv as t ->
                    let id = tvar_spelled tv in
                    if List.exists (Id.equal id) scope then Tany else t
                  | t -> t )
              in
              Some (erase_own (Tfun (List.map Option.get rest_tys, exp)))
            else None
          | _ -> None
        in
        let rec chain_excess base cod excess =
          if excess = [] then base
          else
            let n_here, cod' =
              let cod_cpp c =
                let t = cpp_of_ml env c in
                if cod_is_curried then curry_fun_type t else t
              in
              match Option.map cod_cpp cod with
              | Some (Tfun (dom, _)) when List.length dom < List.length excess
                ->
                let n = List.length dom in
                (n, Option.map (ml_drop_arrows n) cod)
              | _ -> (List.length excess, None)
            in
            let here = List.filteri (fun i _ -> i < n_here) excess in
            let rest = List.filteri (fun i _ -> i >= n_here) excess in
            chain_excess (mk_call base here) cod' rest
        in
        (* A domain the codomain spells [std::any] -- the event of a handler
           that [case_] combined at an erased family -- is opened by code that
           erased the value type's parameters as well, and so reads it at the
           all-[std::any] instantiation (see [crane_all_any]).  A generated
           inductive goes in at that instantiation, through its converting
           constructor, rather than at the one this call site knows. *)
        let erase_params_into_boxes excess =
          let doms =
            match Option.map (cpp_of_ml env) cod_inst with
            | Some (Tfun (dom, _)) -> dom
            | _ -> []
          in
          List.mapi
            (fun i e ->
              match (List.nth_opt doms i, List.nth_opt excess_args i) with
              | Some d, Some (MLrel j) when prints_as_any d -> (
                match
                  Option.map
                    (fun t -> strip_ns_tglob (unfold_cpp_typedef env t))
                    (binder_cpp_type_or_derive env j)
                with
                | Some (Tglob ((GlobRef.IndRef _ as g), (_ :: _ as args), ns))
                  when (not (Table.is_custom g))
                       && not (List.for_all (fun a -> a = Tany) args) ->
                  Cpp_erasure.converting_ctor
                    (Tglob (g, List.map (fun _ -> Tany) args, ns))
                    [e]
                | _ -> e )
              | _ -> e )
            excess
        in
        if ret_is_chainable then
          let excess = List.map (gen_expr ~slot env) excess_args in
          if cod_is_erased then
            let applied = apply_erased_callee base excess in

            (* Args applied to a box come back as a box; the codomain at this
               call's instantiation is what says what that box holds. *)
            let recovered_at =
              let from_cod =
                Option.map
                  (fun c ->
                    cpp_of_ml env (ml_drop_arrows (List.length excess) c) )
                  cod_inst
              in
              (* The instantiated codomain does not always name a type to
                 recover at -- it may itself be erased, the very reason the
                 application went through the boxed convention.  The position
                 the call sits in then says what the value is. *)
              match from_cod with
              | Some c when states_unboxed_target c -> from_cod
              | _ -> expected_ty
            in
            unbox_into recovered_at applied
          else
            (* A codomain instantiated at a type the call erased -- [resum]'s
               [C a b] at [C := IFun], a category over families -- is a
               callable whose C++ type only template deduction knows, and it
               may hand back a box.  The position says what the value is; the
               tolerant cast passes through one that was never boxed. *)
            let excess = erase_params_into_boxes excess in
            let n_first =
              match written_cod with
              | Some (Tfun (dom, _)) -> List.length dom
              | _ -> List.length excess
            in
            match
              if n_first < List.length excess then
                boxed_group_target (List.filteri (fun i _ -> i >= n_first) excess_args)
              else None
            with
            | Some target ->
              let here = List.filteri (fun i _ -> i < n_first) excess in
              let rest = List.filteri (fun i _ -> i >= n_first) excess in
              let r = mk_call (unbox_value target (mk_call base here)) rest in
              ( match expected_ty with
              | Some exp -> CPPconvert (exp, r)
              | None -> r )
            | None ->
            let r = chain_excess base cod_inst excess in
            match (Option.map resolve_tmeta cod_inst, expected_ty) with
            | Some (Miniml.Tdummy Miniml.Ktype), Some t
              when not (prints_as_any t) ->
              Cpp_erasure.unbox_tolerant t r
            | _ -> r
        else
          CPPabort ("untranslatable curried proof term", abort_ty expected_ty) )
    in
    let primary_result =
      match ty with
      | Tfun (dom, cod) ->
        (* Filter domain to exclude type class types (they're now template
           params) and erased types.  Proof params like wf witnesses may
           extract as function types containing dummy_type (e.g.
           Tfun([List<T1>], dummy_type)) rather than plain dummy_type. These
           entries must be removed to match the ML arg list which already
           filters out MLdummy entries. *)
        (* Only a dummy -- an erased proof or type -- is filtered.  A value
           parameter whose type erases, [e : a T] at an erased family, prints
           as [std::any] and is a parameter all the same: dropping it made a
           call one short look saturated. *)
        let dom =
          List.filter
            (fun t ->
              (not (Table.is_typeclass_type_cpp t))
              && (not (is_cpp_dummy_type t))
              && not (is_skipped_cpp_type t) )
            dom
        in
        (* [dom] is the substituted type's, and substitution can erase a
           parameter the declaration still takes -- an argument given at it
           is passed, but has no place in [dom] to be counted against, and
           the call would look saturated one argument early.  Those are
           discounted; see [subst_index_of_orig]. *)
        (* What a partial application is missing is what the declaration
           takes after the given arguments, in the declaration's order.  A
           parameter whose declared type applies a variable is one of them
           even where the substitution erased it -- [fused_trigger]'s event
           [e : F T] at a family [F] erased because it is applied to a section
           variable -- since the application of an erased family is still a
           type of values; it takes the box its type erased to. *)
        let missing_args =
          let from_dom =
            get_eta_args dom
              (List.filteri
                 (fun i _ ->
                   subst_index_of_orig
                     (Param_pos.of_regular ~leading:leading_params i)
                   <> None )
                 args )
          in
          let rec in_declared_order params from_dom =
            match params with
            | [] -> from_dom
            | (o, t) :: rest ->
              let applies_a_variable =
                match resolve_tmeta t with Miniml.Tapp _ -> true | _ -> false
              in
              ( match (subst_index_of_orig o, from_dom) with
              | None, _ when applies_a_variable ->
                Tany :: in_declared_order rest from_dom
              | None, _ -> in_declared_order rest from_dom
              | Some _, d :: from_dom' -> d :: in_declared_order rest from_dom'
              | Some _, [] -> [] )
          in
          (* The parameters past the arguments the call gives. *)
          let untaken =
            List.filter
              (fun (o, _) ->
                match Param_pos.regular_of ~leading:leading_params o with
                | Some r -> r >= List.length args
                | None -> false )
              (Param_pos.positioned fn_param_ml_tys_orig)
          in
          in_declared_order untaken from_dom
        in
        (* When excess args exist (from the ML-level arity split above), do
           NOT eta-expand even if the flattened C++ type has more domain
           elements than ML args.  The mismatch occurs when the callee's
           return type is itself a function type (e.g. [fst] returning
           [Obj -> Path<Obj>]): convert_ml_type_to_cpp_type merges the
           return-type arrows into the domain, inflating [dom_len] beyond the
           ML-level arity.  The excess args will be chained by [wrap_excess]
           below. *)
        (* A mapping that writes no argument placeholder stands for a value,
           not for a call that is short of arguments: it renders as-is, and
           eta-expanding it would state an arity of our own invention.  Its own
           arity is not even knowable here -- the domain a value parameter
           erases to is filtered out of [dom] above, so a dictionary taking an
           erased argument looks one arrow shorter than the parameter it is
           passed as.  A mapping that does write placeholders is a call, and is
           eta-expanded to fill them. *)
        let written_bare =
          args = []
          && ( id_is_typeclass_instance
             || (is_inline_custom id && inline_custom_arg_arity id = Some 0) )
        in
        if written_bare then cglob
        else if missing_args == [] || excess_args <> [] then
          if is_inline_custom id && args = [] then
            (* Nothing is missing, so there is nothing to fill: the template
               renders with what it was given. *)
            cglob
          else mk_call cglob args
        else
          (* Substitute promoted type vars in eta-expanded lambda params. When
             partially applying a function like pick_op<nat_magma>, the domain
             types may contain [Tpromoted "carrier"] — a promoted type var.
             We resolve these to the concrete type from the typeclass instance
             (e.g., unsigned int from nat_magma::carrier). *)
          let missing_args, cod =
            if typeclass_ml_args <> [] && missing_args <> [] then
              let subst_map =
                List.concat_map
                  (fun tc_arg ->
                    match tc_arg with
                    | MLglob (r, _) ->
                      let bindings = Table.get_instance_promoted_types r in
                      List.map
                        (fun (var_name, ml_ty) ->
                          let cpp_ty =
                            cpp_of_ml env ml_ty
                          in
                          (var_name, cpp_ty) )
                        bindings
                    | _ -> [] )
                  typeclass_ml_args
              in
              if subst_map <> [] then
                let rec subst_promoted = function
                  | Tpromoted name ->
                    ( match
                        List.find_opt
                          (fun (vid, _) -> Id.equal vid name)
                          subst_map
                      with
                    | Some (_, concrete) -> concrete
                    | None -> Tpromoted name )
                  | Tconst t -> Tconst (subst_promoted t)
                  | Tfun (d, c) ->
                    Tfun (List.map subst_promoted d, subst_promoted c)
                  | Tshared_ptr t -> Tshared_ptr (subst_promoted t)
                  | t -> t
                in
                (List.map subst_promoted missing_args, subst_promoted cod)
              else
                (missing_args, cod)
            else
              (missing_args, cod)
          in
          (* A variable of the callee's the call left free and no caller
             variable spells alike is the eta-lambda's own to bind (see
             [eta_tparams]); unnamed, it would read as an erased one. *)
          let missing_args, cod =
            let name_free =
              map_cpp_type (function
                | Tvar (Tv_index (i, None))
                  when not
                         (List.exists (Id.equal (Minicpp.tvar_id i))
                            (!tctx).current_type_vars) ->
                  Tvar (Tv_index (i, Some (Minicpp.tvar_id i)))
                | t -> t )
            in
            (List.map name_free missing_args, name_free cod)
          in
          (* The domains the callee's own declaration spells.  [ty] came from
             the ML type {e this call} instantiates, and a higher-kinded class
             parameter is erased there, so a parameter the declaration writes
             [std::optional<T1<std::any>>] arrives as [std::optional<std::any>]
             -- the carrier is simply gone.  It is not gone from the call,
             which has already recovered it into [all_type_args]; and the
             callee's {e uninstantiated} C++ type is where that carrier still
             has a name to be substituted for.  Substituting the explicit
             arguments back into it reconstructs what the declaration says,
             which is the slot each eta parameter has to fit. *)
          let decl_doms, decl_cod =
            (* A phantom position written [void] is one the declaration does
               not use -- [fused_trigger]'s [F], whose only occurrence it
               relaxed to a deduced parameter -- so in a domain it is erased,
               and applied it is the erased type ([void<std::any>] is none). *)
            let subst =
              let by_index =
                List.mapi (fun k t -> (k + 1, t)) written_tvar_args
              in
              fun i ->
                match List.assoc_opt i by_index with
                | Some Tvoid -> Some Tany
                | t -> t
            in
            let collapse_erased_heads =
              map_cpp_type (function Tapply (h, args) -> Minicpp.tapply h args | t -> t)
            in
            match
              Option.map
                (fun t ->
                  collapse_erased_heads
                    (Minicpp.subst_cpp_tvars subst (cpp_of_ml env t)) )
                (find_type_opt id)
            with
            | Some (Tfun (doms, dcod)) -> (doms, Some dcod)
            | _ -> ([], None)
          in
          (* The eta parameters fill the callee's {e trailing} domains; the
             arguments the call already has fill the leading ones. *)
          let slot_dom i =
            List.nth_opt decl_doms
              (List.length decl_doms - List.length missing_args + i)
          in
          let tvars = get_current_type_vars () in
          let erased_eta_param ty =
            Ml_type_util.has_tany_written ty && not (prints_as_any ty)
            && (match ty with Tshared_ptr _ | Tfun _ -> false | _ -> true)
          in
          (* Whether the declaration had anything to say about this call's
             parameters.  It is the same question for the result, so it is
             asked once: a declaration that could not refine a single parameter
             is one whose substitution does not describe this call, and reading
             the result off it would be reading the same wrong thing. *)
          let decl_spoke = ref false in
          let eta_args =
            List.mapi
              (fun i ty ->
                let ty =
                  match slot_dom i with
                  | Some slot ->
                    let refined =
                      Ml_type_util.refine_param_from_slot ~tvars ~slot ty
                    in
                    if refined <> ty then decl_spoke := true;
                    refined
                  | None -> ty
                in
                let wrapped =
                  match ty with
                  | Tshared_ptr _ -> Tref (Lvalue, Tconst ty)
                  (* A parameter erased in part takes whatever instantiation
                     the caller has and is read at this one by
                     [crane_convert] (see [call_args]): a slot spelled
                     [std::function<std::optional<box<Nat>>(...)>] cannot
                     call a lambda declared [std::optional<box<std::any>>],
                     because [std::optional]'s conversion between the two
                     is disabled by the aggregate [box<std::any>]. *)
                  | _ when erased_eta_param ty || mentions_unresolved_promoted ty ->
                    Tref (Lvalue, Tconst Tauto)
                  | _ -> ty
                in
                (wrapped, Some (eta_param_id i)) )
              missing_args
          in
          let eta_arg_reads =
            List.mapi
              (fun i ty ->
                let ty =
                  match slot_dom i with
                  | Some slot -> Ml_type_util.refine_param_from_slot ~tvars ~slot ty
                  | None -> ty
                in
                (* The callee spells a field this scope cannot -- its own
                   instance resolves [state] -- so converting to the spelling
                   here would convert to the file-scope box; the argument goes
                   through to the callee's own parameter instead. *)
                if erased_eta_param ty && not (mentions_unresolved_promoted ty)
                then fun e -> CPPconvert (ty, e)
                else fun e -> e )
              missing_args
          in
          (* A closure's captures are [const] in its body, so a move of one
             is a copy there and cannot leave the next call a moved-from
             value.  Where the closure is single-use ([eta_keep_moves], from
             an [MLletin]) it borrows its scope instead and the moves are the
             enclosing scope's own. *)
          let eta_vars =
            List.mapi
              (fun i _ -> (List.nth eta_arg_reads i) (CPPvar (eta_param_id i)))
              eta_args
          in
          let call_args = args @ eta_vars in
          let call =
            (* The number of arguments the callee itself takes.  An
               inline-custom template stops at its last [%aN] placeholder:
               arguments past it are dropped when it is rendered, and a
               placeholder with no argument cannot be rendered at all.  A
               function whose codomain is a type variable stops at its ML
               arrows, because its declaration had no way to flatten a
               codomain it could not see -- the extra arrows only appear at
               this call site, where the variable is instantiated at a
               function type. *)
            let callee_arity =
              match inline_custom_arg_arity id with
              | Some _ as a -> a
              | None -> (
                match find_type_opt id with
                | Some ml_ty when ml_codomain_is_tvar ml_ty ->
                  Some (count_ml_value_arrows ml_ty)
                | _ -> None )
            in
            match callee_arity with
            | Some arity ->
              (* The eta parameters first finish filling the callee, and only
                 what is left over is applied to its result -- which is a
                 callable, since that is why there were missing arguments to
                 begin with. *)
              let k = max 0 (arity - List.length args) in
              let fill = List.filteri (fun i _ -> i < k) eta_vars in
              let surplus = List.filteri (fun i _ -> i >= k) eta_vars in
              mk_apply (mk_call cglob (args @ fill)) surplus
            | None -> mk_call cglob call_args
          in
          (* The result is the callee's, so it is read off the declaration for
             the same reason the parameters are: what the call returns is
             [std::optional<T1<std::any>>], not the [std::optional<std::any>]
             the erased ML type says. *)
          let cod =
            match decl_cod with
            | Some slot when !decl_spoke ->
              Ml_type_util.refine_param_from_slot ~tvars ~slot cod
            (* A result the substitution erased outright has no other
               statement than the declaration's, which is taken whole
               wherever this scope can spell it. *)
            | Some slot when prints_as_any cod && names_only_scoped_tvars slot
              ->
              slot
            | _ -> cod
          in
          let ret_ty, body =
            if cod = Tvoid then
              (* Void-returning function: execute for side effects, then
                 return without a value. *)
              (None, [Sexpr call; Sreturn None])
            else
              (Some cod, [Sreturn (Some call)])
          in
          (* A type variable the eta-lambda's own signature names and the
             enclosing declaration's head does not is the index the natural
             transformation quantified over.  Eta-expansion is what introduced
             it, so eta-expansion is what has to bind it: written nowhere it
             is a free name, which is how [handle_local_debug]'s index reached
             C++ as a bare [T2] under a head declaring only [T1].

             Binding it is all that is decided here.  Whether it survives as a
             [template <typename>] of the lambda or is erased away is
             {!Minicpp.lambda}'s call, and it turns on whether a parameter
             deduces it -- which is exactly the difference between an index
             the event type still carries ([memM<T2>]) and one erasure took
             out of it (a [LocalE] that is a plain enum). *)
          let eta_tparams =
            let named =
              List.fold_left
                (fun acc t -> Id.Set.union acc (Minicpp.tvar_names t))
                Id.Set.empty
                (cod :: List.map fst eta_args)
            in
            Id.Set.elements
              (List.fold_left
                 (fun acc x -> Id.Set.remove x acc)
                 named
                 (!tctx).current_type_vars )
          in
          (* A use site expecting fewer parameters than the callee takes wants
             a curried closure: the arrows past its arity belong to the
             element type it is generic in, not to the callable itself. *)
          ( match expected_ty with
          | Some (Tfun (exp_dom, _))
            when exp_dom <> [] && List.length exp_dom < List.length eta_args ->
            let n = List.length exp_dom in
            let outer = List.filteri (fun i _ -> i < n) eta_args in
            let inner = List.filteri (fun i _ -> i >= n) eta_args in
            mk_lambda outer None
              [ Sreturn
                  (Some
                     (mk_lambda ~tparams:eta_tparams inner ret_ty body
                        ~capture:Closure ) ) ]
              ~capture:Closure
          | _ ->
            mk_lambda ~tparams:eta_tparams eta_args ret_ty body
              ~capture:(if eta_keep_moves then Immediate else Closure) )
      | _ ->
        if id_is_typeclass_instance && args = [] then
          cglob
        else if is_inline_custom id && args = [] then
          (* Zero-arg inline custom: return the glob directly so the
             template string renders as-is, without an appended (). *)
          cglob
        else if args = [] && not (glob_is_nullary_function id) then
          (* A reference to a global {i value} whose C++ type is not a
             function type (e.g. a state-monad-style [std::function] synonym):
             it is a data member, not a nullary function, so it must not be
             called.  Only globals whose declaration really takes no C++
             parameters -- thunks and those whose every parameter is erased --
             get the [()]. *)
          cglob
        else
          CPPfun_call (call_opaque, cglob, of_reversed args)
    in
    (* Collapse identity inline customs (%a0) at AST level.  This prevents
       unnecessary IIFE wrapping when a void call passes through an identity
       wrapper (e.g. Ceval) and then appears in statement position. *)
    let primary_result =
      match primary_result with
      | CPPfun_call (_, CPPglob (_, _, Some ci), {rev = [single_arg]})
        when inline_shape ci = Some Inline_identity ->
        single_arg
      | _ -> primary_result
    in
    (* Wrap pair-accessor inline custom arguments in any_cast when the
       argument's ML type is erased.  E.g. [fst vs] where [vs : std::any]
       generates [any_cast<pair<any,any>>(vs).first] instead of [vs.first].
       This is the inline-custom analog of the scrutinee any_cast in
       [gen_custom_cpp_case]. *)
    let primary_result =
      match primary_result with
      | CPPfun_call (_, (CPPglob (n, glob_tys, Some ci) as cglob'), {rev = [single_arg]})
        when (match inline_shape ci with
              | Some (Inline_pair_projection _) -> true
              | _ -> false) ->
        let arg_ml_erased =
          (* A variable is erased when its ML type is, or when the C++ type
             it converts to is [std::any] -- a value-dependent type such as
             [symbols_semty gamma] is only opaque after conversion. *)
          let rel_is_erased ty =
            let ty = resolve_tmeta ty in
            is_erased_ml_type ty
            || ml_erases_to_box env ty
          in
          let rec has_magic = function
            (* A coercion around a local variable says nothing on its own: in
               an instance method the class's associated type has already been
               specialised, so the variable holds the concrete pair.  Judge by
               the variable's type when it is known; a coercion is still the
               only evidence available when it is not. *)
            | MLmagic (_, MLrel i) -> (
              match get_env_type_opt i with
              | Some ty -> rel_is_erased ty
              | None -> true )
            | MLmagic (_, _) -> true
            | MLapp (MLglob (r, _), args) as node ->
              (* If the callee is itself a pair accessor (.first/.second) and
                 its product arg was coerced, result is also std::any *)
              let is_pair_accessor =
                match Table.find_custom_opt r with
                | Some s -> (
                  match inline_shape_of_text s with
                  | Inline_pair_projection _ -> true
                  | _ -> false )
                | None -> false
              in
              if is_pair_accessor then
                let inner_args =
                  List.filter (fun x -> match x with MLdummy _ -> false | _ -> true) args
                in
                List.exists has_magic inner_args
              else
                glob_declared_cod_erases r
                (* A declaration that leaves its result a type variable says
                   nothing on its own; the type this call instantiates it to
                   does. *)
                || ( match infer_ml_body_type node with
                   | Some t -> is_boxed_source (cpp_of_ml env t)
                   | None -> false )
            | MLglob (r, _) -> glob_declared_cod_erases r
            | MLapp (MLmagic (_, _), _) -> true
            | MLrel i -> (
              match get_env_type_opt i with
              | Some ty -> rel_is_erased ty
              | None -> false )
            | _ -> false
          in
          if List.length regular_ml_args > 0 then
            has_magic (List.nth regular_ml_args 0)
          else false
        in
        if arg_ml_erased then
          let prod_g_opt =
            (* The first argument the C++ call passes: erased domains carry no
               value, so they are not it. *)
            let first_dom =
              try
                match ml_value_domains (Table.find_type n) with
                | t :: _ -> Some (resolve_tmeta t)
                | [] -> None
              with Not_found -> None
            in
            match first_dom with
            | Some (Miniml.Tglob (g, _, _)) when is_prod_global g -> Some g
            | _ -> None
          in
          ( match prod_g_opt, single_arg with
          | _, CPPany_cast (Tglob (g, cast_args, _), _)
            when is_prod_global g && cast_args <> []
                 && List.for_all prints_as_any cast_args ->
            (* The argument arrived already recovered from its box, and at the
               erased shape [pair<any, any>].  Its components are boxes too, so
               the accessor's result needs the same recovery at the use site as
               when this branch inserts the cast itself --
               {!yields_boxed_component} recognises both shapes. *)
            primary_result
          | _, CPPany_cast _ -> primary_result
          | Some g, _ when (match glob_tys with
                            | [_; _] ->
                              not (List.exists Ml_type_util.has_tany_in_type
                                     glob_tys)
                            | _ -> false) ->
            (* The accessor's own type arguments name both components
               concretely, so the box can be opened at that very shape --
               tolerantly, because a producer that deep-erased stored
               [pair<any,any>], which [crane_any_cast] recovers component by
               component.  What comes out is concrete, so the accessor's
               result needs no further recovery. *)
            mk_call cglob'
              [Cpp_erasure.unbox_tolerant (Tglob (g, glob_tys, [])) single_arg]
          | Some g, _ ->
            (* Tolerantly: the ML type says the argument is a box, but a
               producer that could name the pair's shape may have emitted the
               [pair<any, any>] itself rather than a box around it.
               [crane_any_cast] accepts both -- it opens a box and passes a
               pair already in hand through -- where a plain [any_cast] would
               throw on the latter. *)
            mk_call cglob'
              [ Cpp_erasure.unbox_tolerant
                  (Tglob (g, [Tany; Tany], []))
                  single_arg ]
          | None, _ -> primary_result )
        else
          primary_result
      | _ -> primary_result
    in
    wrap_excess primary_result
  | _ ->
    (* Non-global callee (e.g., a local variable from MLrel). Filter out MLdummy
       args — these are erased type/prop parameters that have no runtime
       representation. Unlike the MLglob case above, there is no type-arg list
       to filter here; we only need to drop value-level dummies. *)
    let args =
      List.filter
        (fun x ->
          match x with
          | MLdummy _ -> false
          | _ -> true )
        args
    in
    (* A class-typed argument is not a value: the concept is met by a type, and
       the method the callee projects declares it as a template parameter.  It
       leaves the argument list for the callee's explicit template arguments,
       which is the only place that parameter can be given. *)
    let tc_args, _, args = split_instance_args env args in
    let gen_callee () =
      match (tc_args, gen_expr env f) with
      | [], e -> e
      | _, CPPscope (b, id, tys) ->
        CPPscope (b, id, tys @ List.filter_map (ml_arg_to_template_type env) tc_args)
      | _, e -> e
    in
    (* The callee's own function type, with an alias standing for one expanded
       -- a single-method class is its method, so [Iter M] {e is} the arrow the
       call goes through. *)
    let callee_fun_ml_ty =
      match f with
        | MLglob (r, tys) when tys <> [] ->
          (match find_type_opt r with
           | Some ty -> Some (Mlutil.type_subst_list tys ty)
           | None -> infer_ml_body_type f)
        | _ ->
          ( match infer_ml_body_type f with
          | Some ty -> Some ty
          | None ->
            (* A local binder typed by name ([c : church]) shows no arrows in
               the term, so its parameter types can only come from the type the
               environment recorded at the binding site.  Only an alias is
               taken: any other binder either carries its arrows in the term or
               is generalised into a deduced callable, which takes each
               argument at the type the argument already has. *)
            ( match f with
            | MLrel i | MLmagic (_, MLrel i) -> (
              match get_env_type_opt i with
              | Some (Miniml.Tglob (GlobRef.ConstRef _, _, _) as ty) -> (
                match expand_ml_fun_alias ty with
                | Miniml.Tarr _ as expanded -> Some expanded
                | _ -> None )
              | _ -> None )
            | _ -> None ) )
    in
    let callee_param_tys =
      (* Erased and class-typed domains take no argument slot, so neither
         takes a place in the list this indexes [args] by. *)
      let rec extract_params = function
        | Miniml.Tarr (t, rest) ->
          ( match resolve_tmeta t with
          | Miniml.Tdummy _ -> extract_params rest
          | t when Table.is_typeclass_type t -> extract_params rest
          | t -> t :: extract_params rest )
        | Miniml.Tmeta {contents = Some t} -> extract_params t
        | _ -> []
      in
      match callee_fun_ml_ty with Some fty -> extract_params fty | None -> []
    in
    let callee_rel_idx = match f with
      | MLrel i | MLmagic (_, MLrel i) -> Some i
      | _ -> None
    in
    let callee_env_ty =
      match callee_rel_idx with
      | Some i -> (try Some (get_env_type i) with _ -> None)
      | None -> None
    in
    let callee_cpp_erased =
      match callee_rel_idx with
      | Some i -> binder_is_boxed i
      | None -> false
    in
    (* A pattern binder whose definition-site field type is a type variable
       still has a concrete C++ type when the scrutinee instantiates that
       variable concretely — [populate_erased_field_env] recorded it in
       [cpp_binder_types] at that concrete type, which is what makes
       [binder_is_boxed] answer no for it.
       Its erased ML type must not be taken at face value here, or a perfectly
       concrete [std::function<uint64_t(uint64_t)>] field gets wrapped in an
       [any_cast] that does not compile. *)
    let callee_known_concrete =
      match callee_rel_idx with
      | Some i when not callee_cpp_erased ->
        ( match pattern_binder_type i with
        | Some t -> not (resolves_to_any_type t)
        | None ->
          (* Likewise for a parameter of the enclosing function: the ambient
             environment may still spell its type as the class/section type
             variable it was abstracted over, while the declaration this body
             belongs to (e.g. a typeclass instance at a function type) pinned
             it to a concrete C++ signature. *)
          ( match get_param_type_by_index i with
          | Some t ->
            (not (is_ml_erased_ty t))
            && not
                 (resolves_to_any_type
                    (convert_ml_type_to_cpp_type env
                       (get_current_type_vars ())
                       t ) )
          | None -> false ) )
      | _ -> false
    in
    (* A callee is only callable through the canonical adapter when nothing
       with a C++ call operator is left of its type -- which is what
       [std::any] means here.  The ML type may say so outright ([Tdummy],
       [Tunresolved], a bare [Tvar]) or only once converted: a type-level
       [Fixpoint] applied to an argument is a perfectly concrete [Tglob] in
       MiniML and still lands on a [using sem = std::any] alias in C++. *)
    let erases_to_any ty =
      is_ml_erased_ty ty
      || ml_erases_to_box env ty
    in
    let callee_is_bare_any =
      callee_cpp_erased
      || ( (not callee_known_concrete)
         &&
         match callee_env_ty with
         | Some ty -> erases_to_any ty
         | None -> false )
      (* Not a local binder: the callee's own inferred type decides. *)
      || ( callee_rel_idx = None
         &&
         match infer_ml_body_type (strip_magic f) with
         | Some t -> erases_to_any t
         | None -> false )
    in
    let callee_has_erased_params =
      callee_is_bare_any ||
      (match callee_env_ty with
      | Some (Miniml.Tarr (param, _)) -> is_ml_erased_ty param
      | _ -> false) ||
      (match callee_rel_idx with
       | Some i ->
         (match pattern_binder_type i with
          | Some (Tfun (params, _)) -> List.exists (fun p -> p = Tany) params
          | _ -> false)
       | None -> false)
    in
    (* [has_unresolved_boxed_arg]: set when an argument is statically known to
       be boxed as [std::any] ([binder_is_boxed]) but the callee's parameter
       type at this position can't be resolved to a concrete C++ type (it is
       itself abstract/erased, e.g. a value-dependent type scheme like
       [S.sem a]).  This happens when the callee is a genuinely-concrete
       function only at C++ template instantiation time (e.g. a functor
       parameter instantiated with a concrete inlined function) — the OCaml
       side cannot know the concrete type to [any_cast] to.  Such calls are
       routed through the [crane_call_erased] runtime helper instead of a
       direct call, so the concrete parameter types can be recovered via
       [std::function] CTAD once C++ instantiates the template. *)
    let has_unresolved_boxed_arg = ref false in
    let arg_slot =
      {slot with deep_erase = slot.deep_erase || callee_has_erased_params}
    in
    let args =
      List.mapi (fun i x ->
      let expr =
        match x with
        | e when ml_value_is_void_call e ->
          wrap_void_call_as_value (gen_expr ~slot:arg_slot env x)
        | MLmagic (_, _) ->
          let expected = param_expected_cpp_ty env callee_param_tys i in
          gen_expr ?expected_ty:expected ~slot:arg_slot env x
        | MLrel j when binder_is_boxed j ->
          let inner = gen_expr ~slot:arg_slot env x in
          let expected = param_expected_cpp_ty env callee_param_tys i in
          ( match expected with
            | Some ty ->
              Cpp_erasure.unbox (erase_type_args_to_any ty) inner
            | None ->
              has_unresolved_boxed_arg := true;
              inner )
        | _ -> gen_expr ~slot:arg_slot env x
      in
      match List.nth_opt callee_param_tys i with
      | Some param_ty -> erase_fn_arg_for_param env param_ty x expr
      | None -> expr) args
    in
    (* Detect over-application: when a local variable's C++ type has fewer
       value-domain arrows than the number of ML args, the call must be split
       into a primary call and a chained application of excess args. Example: [f
       : A -> State S B] applied as [f(a, s')] becomes [f(a)(s')]. *)
    let n_value_dom =
      let rel_idx_f = match f with
        | MLrel i | MLmagic (_, MLrel i) -> Some i
        | _ -> None
      in
      match rel_idx_f with
      | Some i ->
        ( try
            let ty = get_env_type i in
            let n = count_ml_value_arrows ty in
            (* The declaration is what says how the arrows are taken.  A
               parameter the class declares as [A -> m B], whose [m] this
               instance fixes at something itself arrow-shaped, has one domain
               in C++ and two arrows in ML; flattened, the call hands both at
               once to a callable that takes one.  Where the binding site
               recorded a declared type, that is the answer -- but only where
               it takes {e fewer}, since a declaration with more domains is
               the under-application the ML count already handles and a
               re-derived type is not a declaration. *)
            let n =
              match binder_cpp_type i with
              | Some (Tfun (dom, _)) when List.length dom < n ->
                List.length dom
              | _ -> n
            in
            if n < List.length args && ml_codomain_is_tvar ty then
              List.length args
            else n
          with _ -> List.length args )
      | None -> List.length args
    in
    let n_args = List.length args in
    (* Lifting every argument onto the template list still leaves a call. *)
    if n_args = 0 && tc_args = [] then
      (* All args were erased (MLdummy): no function call, just the
         expression itself.  This arises when erased proof arguments
         (e.g. [le n 0] in [Function]-generated [_rect] bodies) are
         applied to a local variable — the proofs are filtered out,
         leaving an empty arg list.  Generating [f()] would be wrong
         because the C++ type has no 0-arg overload. *)
      gen_callee ()
    else if n_args < n_value_dom && n_value_dom > 0 then
      (* Under-application (partial application due to proof erasure).
         The callee expects [n_value_dom] args but only [n_args] are
         provided — the rest were erased proofs in the same
         [MLapp] that have been filtered out.

         Generate a lambda wrapper that captures the provided args and
         forwards them along with fresh parameters for the remaining
         args.  E.g., [f2(n1)] where [f2 : (nat, T1) -> T1] becomes:
         [[&](T1 _pa0) { return f2(n1, _pa0); }]. *)
      let remaining_ml_tys =
        match f with
        | MLrel i ->
          ( try
              let ml_ty = get_env_type i in
              (* Skip [n_args] non-dummy domain entries to find the
                 remaining value-domain types. *)
              let rec skip_and_collect n = function
                | Miniml.Tarr (t, rest) ->
                  ( match resolve_tmeta t with
                  | Miniml.Tdummy _ -> skip_and_collect n rest
                  | t ->
                    if n > 0 then skip_and_collect (n - 1) rest
                    else t :: skip_and_collect 0 rest )
                | Miniml.Tmeta {contents = Some t} -> skip_and_collect n t
                | _ -> []
              in
              skip_and_collect n_args ml_ty
            with _ -> [] )
        | _ -> []
      in
      if remaining_ml_tys <> [] then
        let callee = gen_callee () in
        let pa_params = List.mapi (fun j ml_ty ->
          let cpp_ty = cpp_of_ml env ml_ty in
          (cpp_ty, Some (Id.of_string (Printf.sprintf "_pa%d" j))) )
          remaining_ml_tys
        in
        let pa_exprs = List.map (fun (_, id_opt) ->
          CPPvar (Option.get id_opt)) pa_params in
        mk_lambda pa_params None
          [Sreturn (Some (mk_call callee (args @ pa_exprs)))]
          ~capture:Closure
      else
        mk_call (gen_callee ()) args
    else if n_args > n_value_dom && n_value_dom > 0 then
      let primary = List.rev (safe_firstn n_value_dom args) in
      let excess = List.rev (List.skipn n_value_dom args) in
      CPPfun_call
        (call_opaque,
          CPPfun_call (call_opaque, gen_callee (), of_reversed primary),
          of_reversed excess )
    else
      (* When the callee is a local variable whose ML type is a bare type
         variable (Tvar/Tunresolved), its C++ type is std::any.  std::any
         is not callable, so we must wrap it with std::any_cast to recover the
         std::function type before calling.  Both arg and return types
         default to std::any since the original types are erased.
         The MLmagic wrapper is transparent — peel it to find the MLrel. *)
      let callee_expr = gen_callee () in
      (* Check whether this call returns [std::any] (erased type) but the
         enclosing function expects a concrete type, requiring an
         [std::any_cast<T>] wrapper.  See [ml_codomain_erases_to_any].
         Two callee forms are handled:
         - [MLcase] single-branch record projection whose field type has a
           higher-rank codomain (e.g. [apply : forall A, A -> A] stored as
           [std::function<std::any(std::any)>]).
         - [MLrel] higher-rank callback whose env-type has a [Tvar] codomain
           guarded by [Tdummy] (e.g. [f : forall A, A -> A]). *)
      let result =
        if !has_unresolved_boxed_arg && not callee_is_bare_any then begin
          CPPtolerant_call (callee_expr, args)
        end
        else if callee_is_bare_any then
          apply_erased_curried callee_expr args
        else mk_call callee_expr args
      in
      let n = n_args in
      let erased_cod =
        (* A callee recovered from a bare [std::any] is called through the
           canonical [std::function<std::any(std::any...)>] adapter, so its
           result is a [std::any] no matter what the ML type says. *)
        callee_is_bare_any
        ||
        match f with
        | MLcase (case_ty, _, pv) when Array.length pv = 1 ->
          let (binds, _, _, br_body) = pv.(0) in
          let n_binds = List.length binds in
          let proj_idx =
            match br_body with
            | MLrel i when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | MLmagic (_, MLrel i) when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | _ -> None
          in
          ( match proj_idx with
          | Some idx ->
            ( match case_ty with
            | Tglob (r, _, _) ->
              let all_ft = Table.record_field_types r in
              let non_erased = filter_value_types all_ft in
              ( try ml_codomain_erases_to_any n (List.nth non_erased idx)
                with _ -> false )
            | _ -> false )
          | None -> false )
        | MLrel i ->
          (match get_env_type_opt i with Some ty -> ml_codomain_erases_to_any n ty | None -> false)
        | _ -> false
      in
      recover_boxed_result ~boxed:erased_cod ~expected:expected_ty result
      |> recover_carrier_result ~fun_ty:callee_fun_ml_ty ~n_args:n
           ~want:(position_cpp_ty expected_ty)

(** Generate a single branch of an {!Smatch} if/else-if pattern match chain.

    Produces an {!smatch_branch} record whose body statements live directly
    in the enclosing if-block.

    {b Structured bindings.}  Field accesses use
    [const auto& [d_f0, d_f1] = std::get<T>(v)].  The reference binding is
    required so that [[=]]-capturing closures copy the struct value rather
    than a raw pointer that could dangle after the match scope ends.

    {b [match_i] suffix generation.}  [match_i] is the match-level counter
    (0 for the outermost match).  Nested matches increment the counter so
    binding names get suffixed (e.g. [d_a00], [d_a10]) to avoid shadowing
    outer bindings.

    {b [dummies] mask.}  A [bool list] parallel to [ids]: [true] means the
    pattern variable is actually used (gets a binding); [false] means it is
    [Dummy] (omitted from the structured binding with a placeholder).  This
    avoids generating unused variable warnings in the C++ output.

    @param env      current name environment
    @param typ      the scrutinee's ML type (used to resolve the inductive)
    @param rty      the branch's return type
    @param cname    the constructor's [GlobRef.t]
    @param ids      renamed pattern variable names with types
    @param dummies  parallel mask: [true] = non-Dummy (used), [false] = Dummy
    @param body     the branch body AST
    @param sname    scrutinee expression name (for structured binding access)
    @param match_i  nesting level counter for name suffixing
    @param scrut    the value being matched, shared by every branch *)
and gen_match_branch env (typ : ml_type) rty cname ids dummies body sname
    match_i (scrut : smatch_scrutinee) ~scrut_db =
  let is_owned = scrut.sc_owned in
  let ctor_type = ctor_type_of_match env typ cname in
  let ctor_name = ctor_struct_id_of_ref cname in
  let ctor_struct_name = Id.to_string ctor_name in
  let n_pat_vars = List.length ids in
  (* When the scrutinee is an owned variable (is_owned = true) and we create
     const-ref structured bindings into it ([const auto& [d_a0, d_a1] = ...]),
     moving the scrutinee inside the branch would leave those references
     dangling.  Exclude the shifted scrutinee index from move_owned_vars for
     the duration of the branch so move insertion cannot fire on it. *)
  let exclude_scrutinee =
    if is_owned then Option.map (fun db -> db + n_pat_vars) scrut_db
    else None
  in
  (* Compute ind_ref and field self-reference info early so pat_var_owned
     can exclude shared_ptr-wrapped fields from move tracking. *)
  let ind_ref =
    match cname with
    | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
    | r -> r
  in
  let def_site_field_tys =
    match Table.get_ctor_ip_types_opt cname with
    | Some tys -> tys
    | None -> []
  in
  let non_erased_def_site_field_tys =
    List.filter (fun t -> not (isTdummy t)) def_site_field_tys
  in
  let ind_kn_opt =
    match ind_ref with
    | GlobRef.IndRef (kn, _) -> Some kn
    | _ -> None
  in
  let is_self_or_mutual r =
    globref_equal r ind_ref
    || match r, ind_kn_opt with
       | GlobRef.IndRef (kn2, _), Some kn ->
         MutInd.CanOrd.equal kn2 kn
       | _ -> false
  in
  let field_is_self_or_mutual_ref_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some (Miniml.Tglob (r, _, _)) -> is_self_or_mutual r
    | Some (Miniml.Tmeta {contents = Some (Miniml.Tglob (r, _, _))}) ->
      is_self_or_mutual r
    | _ -> false
  in
  let rec ml_has_self_ref = function
    | Miniml.Tglob (r, args, _) ->
      is_self_or_mutual r || List.exists ml_has_self_ref args
    | Miniml.Tmeta {contents = Some t} -> ml_has_self_ref t
    | Miniml.Tarr (t1, t2) ->
      ml_has_self_ref t1 || ml_has_self_ref t2
    | _ -> false
  in
  let field_has_nested_self_ref_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some (Miniml.Tglob (r, args, _)) when not (is_self_or_mutual r) ->
      List.exists ml_has_self_ref args
    | Some (Miniml.Tmeta {contents = Some (Miniml.Tglob (r, args, _))})
      when not (is_self_or_mutual r) ->
      List.exists ml_has_self_ref args
    | _ -> false
  in
  (* A field recurses THROUGH a boxed-element container (e.g. [list <self>] ->
     [immer::flex_vector<immer::box<self>>]) when the container carries a
     [Boxed Element] wrapper and a self/mutual ref appears in its type args.
     The element box breaks the completeness cycle, so such a field is stored by
     VALUE (matching gen_decls) — it is not shared_ptr-wrapped and must not be
     dereferenced when bound in a match arm. *)
  let rec ml_recurses_through_boxed = function
    | Miniml.Tglob (g, args, _) ->
      ( match Table.find_boxed_wrapper_opt g with
      | Some _ when List.exists ml_has_self_ref args -> true
      | _ -> List.exists ml_recurses_through_boxed args )
    | Miniml.Tmeta {contents = Some t'} -> ml_recurses_through_boxed t'
    | Miniml.Tarr (a, b) ->
      ml_recurses_through_boxed a || ml_recurses_through_boxed b
    | _ -> false
  in
  let field_recurses_through_boxed_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some ty -> ml_recurses_through_boxed ty
    | None -> false
  in
  (* [Crane BoxedFields]: a field boxed for its own type (see
     [Ml_type_util.boxes_field]), and one typed by a parameter. *)
  let def_site_field i p =
    match List.nth_opt non_erased_def_site_field_tys i with Some ty -> p ty | None -> false
  in
  let is_boxed_at_def i = def_site_field i boxes_field in
  let is_param_boxed_at_def i = def_site_field i boxes_param_field in
  let field_is_uptr i =
    not (Table.is_coinductive ind_ref)
    && ( not (field_recurses_through_boxed_at_def i)
         && (field_is_self_or_mutual_ref_at_def i
             || field_has_nested_self_ref_at_def i)
       || is_boxed_at_def i || is_param_boxed_at_def i )
  in
  (* Converse of [exclude_scrutinee]: the structured bindings alias subobjects
     of the owned scrutinee, so moving a field out hollows out part of [o].  If
     the branch body still reads [o] itself, that read may observe the
     moved-from field — sibling arguments of one call are unsequenced, so even
     [Ctor(std::move(a0), f(o))] is wrong.  Drop the whole owned set in that
     case so no field move is emitted. *)
  let scrut_read_in_body =
    match scrut_db with
    | Some db -> Escape.nb_occur_match (db + n_pat_vars) body > 0
    | None -> false
  in
  let pat_var_owned =
    if is_owned && not scrut_read_in_body then
      List.fold_left (fun (acc, j) _ ->
          let db = j + 1 in
          let def_field_idx = n_pat_vars - 1 - j in
          let acc' =
            if not (field_is_uptr def_field_idx) then
              Escape.IntSet.add db acc
            else acc
          in
          (acc', j + 1))
        (Escape.IntSet.empty, 0) ids
      |> fst
    else Escape.IntSet.empty
  in
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
    with_shifted_move_tracking n_pat_vars ~clear_dead:true
      ~add_owned_set:pat_var_owned ?exclude_owned:exclude_scrutinee
      (fun () ->
      let inner_ret =
        match (!tctx).current_cpp_return_type with
        | Some Tvoid -> None
        | rt -> rt
      in
      with_scope @@ fun () ->
      with_cpp_return_type inner_ret (fun () ->
          populate_erased_field_env
            ?scrut_db:(Option.map (fun db -> db + n_pat_vars) scrut_db)
            ~cname ~typ ~env ~n_pat_vars
            ~n_fields:(List.length rev_ids)
            ~non_erased_def_site_field_tys ();
          gen_stmts env_for_body (fun x -> Sreturn (Some x)) body ))
  in
  let tvars = get_current_type_vars () in
(* A non-self-referential field in a type-indexed inductive (no template
     params) whose def-site type contains an unnamed Tvar is stored as
     [std::any] in the struct.  At the match site we recover the ML-known
     type with [std::any_cast<bare_ty>].  This handles every access pattern
     uniformly — fst, snd, or any other function — because the cast is
     applied at the binding site, not at individual use sites. *)
  let scrut_template_args_lazy = lazy (
    let scrut_cpp_ty = cpp_of_ml env typ in
    extract_template_args scrut_cpp_ty
  ) in
  let field_is_wholesale_erased =
    let num_pv = Table.get_ctor_num_param_vars cname in
    fun i ->
      not (field_is_self_or_mutual_ref_at_def i)
      && not (field_has_nested_self_ref_at_def i)
      && (match List.nth_opt non_erased_def_site_field_tys i with
          | Some def_ty when num_pv = 0 ->
            let cpp_ty =
              convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton ind_ref) [] def_ty
            in
            has_unnamed_tvar cpp_ty
          | Some (Miniml.Tvar (_, k)) ->
            let scrut_targs = Lazy.force scrut_template_args_lazy in
            (match List.nth_opt scrut_targs (k - 1) with
             | Some t -> resolves_to_any_type t
             | None -> false)
          | _ -> false)
  in
  let field_bindings =
    List.mapi
      (fun i (_var_name, ml_ty) ->
        let binding_name = binding_names_arr.(i) in
        (* A field needs dereferencing if:
           1. It's a direct self/mutual ref at the definition site
              (stored as shared_ptr in the struct), OR
           2. The def-site field type is Tvar (type parameter) that resolves
              to shared_ptr<T> via template substitution, where T is a
              value-type inductive in method_self_ns.  This happens when a
              container like List<shared_ptr<tree>> stores elements via
              template parameter t_A = shared_ptr<tree>. Direct struct
              fields (Tglob at def-site) are bare value types. *)
        (* Convert using empty ns.  For value-type self/mutual fields the
           expression substituted into the branch body is dereferenced, but the
           structured binding itself still has the stored field type
           [shared_ptr<T>].  Loopify uses this metadata to infer frame field
           types for expressions like [d_a0.get()] and [*d_a0]. *)
        let bare_field_cpp_ty =
          cpp_of_ml env ml_ty
        in
        let storage_field_cpp_ty =
          convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton ind_ref)
            tvars
            ml_ty
        in
        (* A non-coinductive field is shared_ptr-wrapped only for UNIFORM
           self-recursion.  Non-uniform recursion (e.g. tree<pair<T,T>> inside
           tree<T>) stores as a bare value type.  Find the self/mutual reference
           anywhere in the ML type (direct or nested in type args) and check if
           its type arguments match the parent's params uniformly. *)
        let is_uniform_self_ref_at_def i =
          match List.nth_opt non_erased_def_site_field_tys i with
          | Some ty -> begin
            match find_self_ref_args ~is_self_or_mutual ty with
            | Some args ->
              let n_params = Table.get_ctor_num_param_vars cname in
              List.length args = n_params
              && List.for_all (fun (j, arg) ->
                match arg with
                | Miniml.Tvar (_, k) -> k = j + 1
                | Miniml.Tmeta {contents = Some (Miniml.Tvar (Schematic, k))}
                | Miniml.Tmeta {contents = Some (Miniml.Tvar (Rigid, k))} -> k = j + 1
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
          && not (Table.is_coinductive ind_ref)
        in
        (* The struct holds a [crane::field] for a type-parameter field
           unless it erased the field outright. *)
        let is_param_boxed =
          (not is_sptr_self_ref) && is_param_boxed_at_def i
          && (not (Table.is_coinductive ind_ref))
          && (not (field_is_wholesale_erased i))
          && bare_field_cpp_ty <> Tany
        in
        let field_cpp_ty =
          if is_sptr_self_ref then
            (* All self/mutual refs (direct or nested-in-custom): struct field
               is shared_ptr<bare>.  After deref, the binding has type bare_ty
               which matches the API type directly — no element-wise conversion
               needed.  Using storage_field_cpp_ty here would store inner
               self-refs as shared_ptr<T> inside the custom container, but
               there is no element-wise converter from List<shared_ptr<T>> to
               List<T>, so we must keep elements as bare values. *)
            Tshared_ptr bare_field_cpp_ty
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
               field's def-site type is a bare Tvar (not self-ref), but at the
               use site it resolves to List<T> which ns-wraps to shared_ptr. *)
            if non_erased_def_site_field_tys <> []
               && not (field_is_self_or_mutual_ref_at_def i)
               && not (field_has_nested_self_ref_at_def i)
               && contains_shared_ptr storage_field_cpp_ty
            then bare_field_cpp_ty
            else storage_field_cpp_ty
        in
        let used = dummies_arr.(i) in
        let read =
          if is_sptr_self_ref then Read_through_pointer
          else if is_param_boxed then Read_unboxed
          else Read_as_bound
        in
        (binding_name, field_cpp_ty, read, used))
      rev_ids
  in
  let field_bindings_arr = Array.of_list field_bindings in
  let rec expr_has_lambda = function
    | CPPfun_call (_, CPPlambda {cl_body = body; _}, _) ->
      (* IIFE: lambda is invoked immediately, so reference captures are safe.
         Only check the lambda body for nested non-IIFE lambdas. *)
      List.exists stmt_has_lambda body
    | CPPlambda {cl_capture = Closure; _} ->
      (* [=] value-capture: non-coinductive self-ref fields (shared_ptr) need
         pre-extraction into a value binding before the lambda is entered. *)
      true
    | CPPlambda {cl_body = body; cl_capture = Immediate; _} ->
      (* [&] ref-capture: shared_ptr fields are captured by reference — fine.
         Check the body for nested [=] lambdas that would need pre-extraction. *)
      List.exists stmt_has_lambda body
    | e ->
      let found = ref false in
      iter_expr_children
        ~on_expr:(fun e' -> if expr_has_lambda e' then found := true)
        ~on_stmts:(fun stmts ->
          if List.exists stmt_has_lambda stmts then found := true)
        e;
      !found
  and stmt_has_lambda = function
    | Sreturn (Some e) | Sexpr e -> expr_has_lambda e
    | Sasgn (_, _, e) -> expr_has_lambda e
    | Sif (c, t, f) ->
      expr_has_lambda c || List.exists stmt_has_lambda t
      || List.exists stmt_has_lambda f
    | Sswitch (scrut, _, branches, default) ->
      expr_has_lambda scrut
      || List.exists (fun (_, body) -> List.exists stmt_has_lambda body) branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Smatch (scrut, branches, default) ->
      expr_has_lambda scrut.sc_expr
      || List.exists
        (fun br -> List.exists stmt_has_lambda br.smb_body)
        branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Scustom_case (_, scrut, _, branches, _) ->
      expr_has_lambda scrut
      || List.exists
           (fun (_, _, body) -> List.exists stmt_has_lambda body)
           branches
    | Sassign_expr (obj, e) -> expr_has_lambda obj || expr_has_lambda e
    | Swhile (c, body) -> expr_has_lambda c || List.exists stmt_has_lambda body
    | Sblock body -> List.exists stmt_has_lambda body
    | Sblock_custom (_, _, _, _, args, _) -> List.exists expr_has_lambda args
    | _ -> false
  in
  let branch_has_lambda = List.exists stmt_has_lambda body_stmts in
  (* True when the enclosing function returns a coinductive type and will
     wrap each branch result in a [lazy_] thunk via [cofix_wrap].  The
     thunk is a [CPPlambda] that captures by [=], so non-coinductive
     self-ref (shared_ptr) fields bound in the branch need pre-extraction
     before the lambda to ensure they are captured as value types.
     This flag triggers pre-extraction even when [branch_has_lambda] is
     false (because the lambda is added externally by [inline_iife]). *)
  let return_type_is_coinductive =
    match (!tctx).current_cpp_return_type with
    | Some (Tglob (r, _, _)) -> Table.is_coinductive r
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
      (fun stmts (i, (var_name, _ml_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, read, _) = field_bindings_arr.(i) in
          let bare_ty = cpp_of_ml env _ml_ty in
          (* Pre-extract fields stored as shared_ptr when the branch body
             contains a lambda (or the return type is coinductive), so the
             lambda captures the value type rather than the shared_ptr.
             Only non-coinductive self-refs (is_uptr = true) need this:
             all formerly-unique_ptr fields have is_uptr set, and shared_ptr
             (coinductive or generic container fields) is copyable and can
             be captured directly. *)
          let is_uptr_field = read = Read_through_pointer in
          let subst_expr =
            if read = Read_unboxed then
              mk_call (CPPrt Crane_rt.Unbox_field) [CPPvar binding_name]
            else if is_uptr_field && branch_needs_sptr_preextract then
              CPPvar (Id.of_string (Id.to_string binding_name ^ "_value"))
            else if is_uptr_field then
              (* field_ty = Tshared_ptr storage_inner.  Deref the outer
                 shared_ptr, then convert storage_inner → bare_ty if they
                 differ (e.g. optional<shared_ptr<T>> → optional<T>). *)
              let deref = CPPderef (CPPvar binding_name) in
              (match field_ty with
               | Tshared_ptr storage_inner when storage_inner <> bare_ty ->
                 gen_type_conversion_expr ~src_ty:storage_inner ~dst_ty:bare_ty deref
               | _ -> deref)
            else if field_ty <> bare_ty
                    && contains_shared_ptr field_ty then
              gen_type_conversion_expr ~src_ty:field_ty ~dst_ty:bare_ty
                (CPPvar binding_name)
            else if field_is_wholesale_erased i
                    && not (resolves_to_any_type bare_ty) then
              (* [resolves_to_any_type] (not just [prints_as_any]) so that a
                 field whose declared type is itself an erased alias (e.g.
                 [symbol_semty = std::any]) is NOT wrapped in a spurious
                 [any_cast<symbol_semty>]: the binding already holds the erased
                 value directly, and casting a [std::any] holding a container to
                 [std::any] would throw at runtime.  Only genuinely concrete
                 target types are unwrapped here. *)
              (match strip_ns_tglob bare_ty with
               | Tglob (g, [_], _) when is_list_global g && not (Table.is_custom g) ->
                 let list_any_ty =
                   match bare_ty with
                   | Tnamespace (ns_g, _) -> Tnamespace (ns_g, Tglob (g, [Tany], []))
                   | _ -> Tglob (g, [Tany], [])
                 in
                 Cpp_erasure.converting_ctor bare_ty
                   [Cpp_erasure.unbox list_any_ty (CPPvar binding_name)]
               | Tglob (g, [elem_ty], _) when Ml_type_util.is_custom_list_global g ->
                 let erased_elem = erase_type_to_any elem_ty in
                 let cast_ty =
                   if erased_elem = Tany then bare_ty
                   else Tglob (g, [erased_elem], [])
                 in
                 Cpp_erasure.unbox cast_ty (CPPvar binding_name)
               | _ -> Cpp_erasure.unbox bare_ty (CPPvar binding_name))
            else
              CPPvar binding_name
          in
          List.map (local_var_subst_stmt ~keep_cast:true var_name subst_expr)
            stmts
        else
          stmts )
      body_stmts
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let uptr_value_bindings =
    List.filter_map
      (fun (i, (_var_name, ml_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, read, _) =
            field_bindings_arr.(i)
          in
          let is_uptr_field = read = Read_through_pointer in
          if is_uptr_field && branch_needs_sptr_preextract then
            let bare_ty =
              cpp_of_ml env ml_ty
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
            let deref = CPPderef (CPPvar binding_name) in
            let (binding_name', field_ty', _, _) = field_bindings_arr.(i) in
            let _ = binding_name' in
            let rhs =
              match field_ty' with
              | Tshared_ptr storage_inner when storage_inner <> bare_ty ->
                gen_type_conversion_expr ~src_ty:storage_inner ~dst_ty:bare_ty deref
              | _ -> deref
            in
            Some
              (Sasgn
                 ( value_id,
                   Declare (Tref (Lvalue, Tconst bare_ty)),
                   rhs ))
          else None
        else None)
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let body_stmts = uptr_value_bindings @ body_stmts in
  (* Use std::get (smb_var = Some) when any constructor field is actually used;
     otherwise use holds_alternative only (smb_var = None). *)
  let has_used_fields = List.exists Fun.id dummies in
  { smb_ctor_type = ctor_type;
    smb_var = (if has_used_fields then Some sname else None);
    smb_field_bindings =
      (if has_used_fields then
         List.map (fun (n, ty, _read, used) -> (n, ty, used)) field_bindings
       else []);
    smb_extra_conds = [];
    smb_body = body_stmts }

(** Generate C++ pattern matching for an [MLcase].

    Dispatches based on the inductive's structure:
    - {b Enum types}: generate a [switch] statement on tag values
      ({!gen_enum_branches}).
    - {b Variant types}: generate an if/else-if chain using
      [std::holds_alternative] guards and [std::get] structured bindings
      ({!gen_match_branch}).

    {b Type resolution.}  When the match type contains unresolved [Tvar]s,
    attempts to resolve them from [env_types] so that field types and
    constructor type parameters are concrete for code generation. *)
and gen_cpp_case (typ : ml_type) t env pv =
  (* When the match type annotation has unresolved Tvars, try to resolve from
     context. This handles monomorphic functions where MLcase has Tvar but the
     concrete type is known. *)
  let rec resolvable_here = function
    | Miniml.Tglob (g, ts, _) ->
      ( (not (Table.is_promoted_type_var g))
      || promoted_var_resolution g <> None )
      && List.for_all resolvable_here ts
    | Miniml.Tarr (a, b) -> resolvable_here a && resolvable_here b
    | Miniml.Tmeta {contents = Some t} -> resolvable_here t
    | _ -> true
  in  let resolve_tvar_type typ candidate =
    match (typ, candidate) with
    | Miniml.Tglob (r1, _, _), Miniml.Tglob (r2, _, _)
      when globref_equal r1 r2
           && has_tvar typ
           && (not (has_tvar candidate))
           (* Only a candidate that erased nothing replaces the annotation
              whole: [observe t] at a family its call erased is [itreeF D _]
              where the annotation knows the family. *)
           && not (ml_type_contains_erased candidate) -> candidate
    | _ ->
      (* The annotation may state the inductive and leave its argument open --
         [EOU _] for a call whose declared result is [EOU ptr] -- and then the
         match spells [std::any] where the value has a type.  The candidate is
         the declaration the scrutinee was produced by, so it may fill what the
         annotation left open, and nothing more: see
         {!Ml_type_util.refine_erased}.  A promoted variable this scope cannot
         resolve is not an answer, and neither is an erased one. *)
      Ml_type_util.refine_erased
        ~writable:(fun t ->
          resolvable_here t
          && names_only_scoped_tvars (cpp_of_ml env t)
          && not (Ml_type_util.has_tany_in_type (cpp_of_ml env t)) )
        typ candidate
  in
  let typ =
    match t with
    | MLrel i | MLmagic (_, MLrel i) ->
      (* Scrutinee is a variable reference — use its concrete type. Try
         env_types first (correctly tracks let-bound variables with shifted de
         Bruijn indices), then fall back to param_types. Unwrap Tmeta wrappers
         since env_types may store types in Tmeta form. *)
      let rec unwrap_tmeta = function
        | Miniml.Tmeta {contents = Some t} -> unwrap_tmeta t
        | t -> t
      in
      let env_ty_opt =
        try
          let env_ty = unwrap_tmeta (get_env_type i) in
          match env_ty with
          | Miniml.Tglob _ -> Some env_ty
          | _ -> None
        with _ -> None
      in
      let typ =
        match env_ty_opt with
        | Some let_ty -> resolve_tvar_type typ let_ty
        | None -> (
          match get_param_type_by_index i with
          | Some (Miniml.Tglob _ as param_ty) -> resolve_tvar_type typ param_ty
          | _ -> typ )
      in
      (* The variable's declared C++ type is what its value is: where it
         erased a position -- a pattern field of a plain family parameter,
         [Sum1<BE, cE, std::any>] inside [Sum1<AE, _, X>], whose ML type
         says [X] -- the match spells it erased too. *)
      let rec erase_as ml cpp =
        match (resolve_tmeta ml, Ml_type_util.unqualify_ty cpp) with
        | Miniml.Tglob (g, mas, x), Tglob (g', cas, _)
          when GlobRef.CanOrd.equal g g' && List.length mas = List.length cas ->
          Miniml.Tglob
            ( g,
              List.map2
                (fun m c ->
                  if prints_as_any c && not (ml_type_contains_erased m) then
                    Miniml.Tunknown
                  else erase_as m c )
                mas cas,
              x )
        | m, _ -> m
      in
      ( match binder_cpp_type i with
      | Some bt -> erase_as typ (strip_cpp_ref_const bt)
      | None -> typ )
    | _ ->
      (* Anything else: the scrutinee's own structure says what it produces,
         through the one reader -- a call's instantiated codomain, a
         projection's field type.  Reading it here rather than re-deriving a
         callee's return type keeps a projection, which is an [MLcase] and not
         an application at all, from being left out. *)
      ( match
          ( match ml_projection_field_type (strip_magic t) with
          | Some _ as c -> c
          | None -> infer_ml_body_type t )
        with
      | Some cand -> resolve_tvar_type typ cand
      | None -> typ )
  in
  (* When the type is still unresolved (Tunresolved / Tdummy / non-Tglob),
     recover the inductive from the first branch's constructor pattern -- a
     constructor determines the inductive it belongs to, so this is sound
     wherever the scrutinee's own type failed to resolve.  It happens for a
     dependent field stored as [std::any] (sigT's second projection) and for
     the body of an instance method, which is extracted against the class's
     erased carrier and so carries no type for the scrutinee at all. *)
  let scrut_is_mlmagic_case = match t with MLmagic (_, _) -> true | _ -> false in
  let typ =
    match typ with
    | Miniml.Tglob _ -> typ
    | _ ->
      ( try
          let _, _, pat0, _ = pv.(0) in
          match pat0 with
          | Pusual (GlobRef.ConstructRef (ip, _))
          | Pcons (GlobRef.ConstructRef (ip, _), _) ->
            Miniml.Tglob (GlobRef.IndRef ip, [], [])
          | _ -> typ
        with _ -> typ )
  in
  (* Check if this is an enum inductive type *)
  let is_enum =
    match typ with
    | Miniml.Tglob (GlobRef.IndRef (kn, i), _, _) ->
      is_enum_inductive (GlobRef.IndRef (kn, i))
    | _ -> false
  in
  (* Check if this is a flat single-constructor inductive type *)
  let is_flat_match =
    match typ with
    | Miniml.Tglob (r, _, _) -> Table.is_flat_inductive r
    | _ -> false
  in
  if is_enum then (* Generate switch-based matching wrapped in IIFE *)
    let ind_ref =
      match typ with
      | Miniml.Tglob (r, _, _) -> r
      | _ ->
        CErrors.anomaly (Pp.str "gen_case_cpp: enum type expected to be Tglob")
    in
    let scrutinee =
      recover_erased_scrutinee env ~is_magic:scrut_is_mlmagic_case typ
        (gen_expr env t)
    in
    let rec gen_enum_branches = function
      | [] -> []
      | (ids, _rty, p, body) :: cs ->
      match p with
      | Pusual r | Pcons (r, _) ->
        let _ids', env' =
          push_vars'
            (List.rev_map
               (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
               ids )
            env
        in
        let ctor_name =
          match r with
          | GlobRef.ConstructRef ((kn, i), cidx) ->
            Id.of_string (Common.enum_ctor_name_of_ref kn i cidx)
          | _ -> Id.of_string (Common.enum_ctor_name_of_id
                   (Table.safe_basename_of_global r))
        in
        let body_stmts = gen_stmts env' (fun x -> Sreturn (Some x)) body in
        (ctor_name, body_stmts) :: gen_enum_branches cs
      | Pwild | Prel _ | Ptuple _ -> gen_enum_branches cs
    in
    let gen_default_stmts () =
      let wild_br =
        Array.to_list pv
        |> List.find_opt (fun (_, _, p, _) -> match p with Pwild -> true | _ -> false)
      in
      Option.map (fun (_, _, _, body) -> gen_stmts env (fun x -> Sreturn (Some x)) body) wild_br
    in
    let void_ret = iife_void_return env typ pv in
    let branches, default =
      let ret =
        if void_ret = Some Tvoid then Some Tvoid
        else (!tctx).current_cpp_return_type
      in
      with_cpp_return_type ret (fun () ->
          let branches = gen_enum_branches (Array.to_list pv) in
          (branches, gen_default_stmts ()) )
    in
    let body = [Sswitch (scrutinee, ind_ref, branches, default)] in
    let iife_ret_opt =
      match void_ret with
      | Some _ as v -> v
      | None -> iife_closure_return env typ pv body
    in
    mk_iife iife_ret_opt body
  else
    (* Generate if/else-if pattern matching using [std::holds_alternative]
       and [std::get].  Produces an {!Smatch} node wrapped in an IIFE. *)
    let scrut_db = scrutinee_binder t in
    (* Allocate a unique [_m] name for this match level.  All branches of
       the same match reuse this name (each [if (auto* _m = ...)] creates
       its own scope); nested matches get the next name ([_m0], [_m1]). *)
    let match_i = (!tctx).match_param_counter in
    tctx := { !tctx with match_param_counter = match_i + 1 };
    let sname =
      Id.of_string
        ( if match_i = 0 then "_m"
          else "_m" ^ string_of_int (match_i - 1) )
    in
    (* Generate scrutinee expression.  Clear [move_dead_after] to prevent
       [std::move(x)->v()] use-after-move — the scrutinee is referenced
       across all branches. *)
    let saved_dead_visit = (!tctx).move_dead_after in
    tctx := { !tctx with move_dead_after = Escape.IntSet.empty };
    let scrut_expr = gen_expr env t in
    tctx := { !tctx with move_dead_after = saved_dead_visit };
    let scrut_expr =
      recover_erased_scrutinee env ~is_magic:scrut_is_mlmagic_case typ scrut_expr
    in
    (* Methodification rewrites the receiver parameter to [this] (or [*this]
       when the value is needed).  Ownership analysis may still mark the
       original parameter as owned, but a const method cannot decompose the
       receiver through [v_mut()].  Treat receiver matches as borrowed so
       generated access goes through [v()]. *)
    (* A shared variant is matched by reading: a field taken out of it is a
       count bump, while decomposing it through [v_mut()] would first copy a
       block anyone else holds. *)
    let scrut_is_shared =
      match typ with Tglob (r, _, _) -> Table.is_shared_variant r | _ -> false
    in
    (* Whether this match may consume the scrutinee.  A shared value is
       matched by borrowing all the same -- its fields are count bumps away --
       and is consumed only by block reuse below. *)
    let scrut_consumable =
      match scrut_expr with
      | CPPthis | CPPderef CPPthis -> false
      | _ -> (
        match scrut_db with
        | Some i -> Escape.IntSet.mem i (!tctx).move_owned_vars
        | None -> false )
    in
    let scrut_is_owned = scrut_consumable && not scrut_is_shared in
    (* Build variant accessor.  All inductives (including coinductives)
       are value types and use [scrut.v()] (dot access).  Exception:
       [this] is always a pointer, so method bodies use [this->v()].
       For flat types (no variant wrapper), use the scrutinee directly. *)
    let scrut_is_ptr =
      match scrut_expr with CPPthis -> true | _ -> false
    in
    let scrut_v =
      if is_flat_match then
        scrut_expr
      else if scrut_is_ptr then
        CPPaccess_call (Aarrow, scrut_expr, Id.of_string "v", [])
      else
        mk_call (CPPaccess (Adot, scrut_expr, Id.of_string "v")) []
    in
    let scrut =
      { sc_expr = scrut_v;
        sc_access = Adot;
        sc_owned = scrut_is_owned;
        sc_flat = is_flat_match }
    in
    (* Push renamed pattern variables into the environment, register their
       types in [env_types], and compute a dummies mask (true = non-Dummy).
       The caller is responsible for saving/restoring env_types. *)
    let process_match_pattern_vars ids env =
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
             ids )
          env
      in
      let env_ids' = retype_dependent_params typ ids' in
      push_binders env env_ids';
      let dummies =
        List.map (fun (x, _) -> match x with Dummy -> false | _ -> true) ids
      in
      (ids', env', dummies)
    in
    (* Generate one {!smatch_branch} per constructor pattern, collecting
       a wildcard body from [Pwild] / [Prel]. *)
    let alternatives = begin_alternatives () in
    let rec gen_branches = function
      | [] -> ([], None)
      | (ids, rty, p, body) :: cs ->
      match p with
      | Pusual r | Pcons (r, _) ->
        let saved_env_types = (!tctx).env_types in
        let saved_erased = save_erased_env () in
        let ids', env', dummies = process_match_pattern_vars ids env in
        enter_alternative alternatives;
        let br =
          gen_match_branch env' typ rty r ids' dummies body sname
            match_i scrut ~scrut_db
        in
        leave_alternative alternatives;
        restore_env_types saved_env_types;
        restore_erased_env saved_erased;
        let rest, wild = gen_branches cs in
        (br :: rest, wild)
      | Pwild | Prel _ ->
        enter_alternative alternatives;
        let body_stmts =
          gen_stmts env (fun x -> Sreturn (Some x)) body
        in
        leave_alternative alternatives;
        ([], Some body_stmts)
      | Ptuple _ -> gen_branches cs
    in
    let branches, wildcard = gen_branches (Array.to_list pv) in
    end_alternatives alternatives;
    let iife_ret_opt =
      match iife_void_return env typ pv with
      | Some _ as v -> v
      | None ->
        iife_closure_return env typ pv [Smatch (scrut, branches, wildcard)]
    in
    (* Perceus reuse (Crane Reuse): rebuild a same-inductive constructor in
       a cell the match frees instead of allocating, via the [<ctor>__reuse]
       factory.  Dual path guarded by [scrut.v().index()==branch_idx] and a
       uniqueness test; otherwise the normal [Smatch].  Which cell:
       - a shared variant: the scrutinee's own block, when no other value
         holds it -- the fields are moved out, and the factory writes the new
         ones in (or allocates, if the rebuilt constructor is another);
       - otherwise, under NonAtomicRc (crane::rc carries the reusable control
         block): the matched constructor's first recursive child's cell, when
         unique -- a map's node has two, and its rebuild recycles the first.
       Only for an owned, non-coinductive scrutinee. *)
    let reuse_stmts_opt =
      if Table.reuse () && Table.reuse_loopify_ok ()
         && (if scrut_is_shared then scrut_consumable
             else Table.non_atomic_rc () && scrut_is_owned)
         && (not is_flat_match) && (not is_enum)
         && (match typ with Tglob (r, _, _) -> not (Table.is_coinductive r) | _ -> true)
      then
        let scrut_cpp_ty = cpp_of_ml env typ in
        (* The recycled cell is a [crane::rc] over the *scrutinee's* inductive
           instance, so it can only be handed to a [__reuse] factory that
           rebuilds that same instance.  A type-changing function such as
           [mapl : (A -> B) -> lst A -> lst B] matches on [lst A] but rebuilds
           [lst B]: the two differ in size, alignment and destructor, so
           recycling the cell is not merely a type error but unsound.  Require
           the branch to reconstruct exactly the scrutinee's type. *)
        let branch_rebuilds_scrut_ty branch_idx =
          let _ids, rty, _pat, _body = pv.(branch_idx) in
          Ml_type_util.cpp_ty_eq scrut_cpp_ty
            (cpp_of_ml env rty)
        in
        (* The arm moves the scrutinee's fields out and recycles its child's
           cell, so a body that reads the scrutinee whole -- an association
           list's [add] returning [(k, x) :: s] -- would read what is left. *)
        let body_reads_scrutinee branch_idx =
          let ids, _, _, body = pv.(branch_idx) in
          match scrut_db with
          | Some db -> Mlutil.ast_occurs (db + List.length ids) body
          | None -> false
        in
        let try_cand (branch_idx, matched_ctor, _ar, tail_ctor, _ta) =
          if not (branch_rebuilds_scrut_ty branch_idx) then None
          else if body_reads_scrutinee branch_idx then None
          else
          let ids, _rty, _pat, body = pv.(branch_idx) in
          let ids', env' =
            push_vars'
              (List.rev_map
                 (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
                 ids)
              env
          in
          let rev_ids' = List.rev ids' in
          let dummies_arr =
            Array.of_list
              (List.rev
                 (List.map
                    (fun (x, _) -> match x with Dummy -> false | _ -> true)
                    ids))
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
            match Table.get_ctor_ip_types_opt matched_ctor with
            | Some tys -> List.filter (fun t -> not (isTdummy t)) tys
            | None -> []
          in
          let self_ref =
            match typ with Tglob ((GlobRef.IndRef _ as r), _, _) -> Some r | _ -> None
          in
          let is_uniform_self t =
            match (Mlutil.ml_resolve t, self_ref) with
            | Miniml.Tglob (r, args, _), Some r0 when GlobRef.CanOrd.equal r r0 ->
              List.for_all Fun.id
                (List.mapi
                   (fun j a ->
                     match Mlutil.ml_resolve a with
                     | Miniml.Tvar (_, k) -> k = j + 1
                     | _ -> false )
                   args )
            | _ -> false
          in
          let rec mentions_family t =
            match (Mlutil.ml_resolve t, self_ref) with
            | Miniml.Tglob (GlobRef.IndRef (kn, _), _, _), Some (GlobRef.IndRef (kn0, _))
              when MutInd.CanOrd.equal kn kn0 ->
              true
            | Miniml.Tglob (_, args, _), _ -> List.exists mentions_family args
            | Miniml.Tarr (a, b), _ -> mentions_family a || mentions_family b
            | _ -> false
          in
          let reads =
            List.mapi
              (fun i _ ->
                if not dummies_arr.(i) then Some `Unused
                else
                  match List.nth_opt def_tys i with
                  | Some t when is_uniform_self t -> Some `Child
                  | Some t when Ml_type_util.boxes_field t -> Some `Deref
                  | Some t when Ml_type_util.boxes_param_field t -> Some `Unbox
                  | Some t when mentions_family t -> None
                  | Some _ -> Some `Move
                  | None -> None )
              rev_ids'
          in
          (* The constructor rebuilt must have somewhere to put the cell: a
             shared variant's block needs fields to hold, a child's cell needs
             a field holding the inductive itself.  [nil] has neither. *)
          let tail_tys =
            Option.default [] (Table.get_ctor_ip_types_opt tail_ctor)
          in
          let reused_cell =
            if List.mem None reads then None
            else if scrut_is_shared then
              if def_tys <> [] && List.exists (fun t -> not (isTdummy t)) tail_tys
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
            let saved_env_types = (!tctx).env_types in
            push_binders env ids';
            let scrut_vmut =
              if scrut_is_ptr then
                CPPaccess_call (Aarrow, scrut_expr, Id.of_string "v_mut", [])
              else
                mk_call (CPPaccess (Adot, scrut_expr, Id.of_string "v_mut")) []
            in
            (* Name the alternative rather than number it: the branch index
               and the variant position coincide, but [std::get<typename
               T::Ctor>] says which constructor is being reused. *)
            let matched_alt =
              Id.of_string_soft (ctor_struct_name_of_ref matched_ctor)
            in
            (* The field by the name the constructor's struct gives it --
               [l] for [list]'s tail, not the positional [a1]. *)
            let rf i =
              CPPaccess
                ( Adot,
                  CPPstd_get (Tqualified (scrut_cpp_ty, matched_alt), Some scrut_vmut),
                  Common.lookup_ctor_field_name ~owner:matched_ctor
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
                   (fun (i, (var_name, ml_ty)) read ->
                     let bind e = [Sasgn (var_name, Declare (cpp_of_ml env ml_ty), e)] in
                     match read with
                     | Some `Unused | None -> []
                     (* The token: its value is moved out, owned, so the
                        recursion propagates reuse; the cell stays behind as
                        the token. *)
                     | Some `Child when moved_child i -> bind (CPPmove (CPPderef (rf i)))
                     | Some (`Child | `Deref) -> bind (CPPderef (rf i))
                     | Some `Unbox -> bind (mk_call (CPPrt Crane_rt.Unbox_field) [rf i])
                     | Some `Move -> bind (CPPmove (rf i)) )
                   (List.mapi (fun i x -> (i, x)) rev_ids')
                   reads)
            in
            let tok, unique_cond =
              match reused_cell with
              | `Block ->
                (scrut_expr, mk_call (CPPaccess (Adot, scrut_v, Id.of_string "unique")) [])
              | `Child_cell k ->
                ( rf k,
                  CPPbinop
                    ( Beq,
                      mk_call (CPPaccess (Adot, rf k, Id.of_string "use_count")) [],
                      CPPint 1 ) )
            in
            let body_stmts =
              with_reuse_token (Some (tok, tail_ctor)) (fun () ->
                  gen_stmts env' (fun x -> Sreturn (Some x)) body )
            in
            restore_env_types saved_env_types;
            Some (branch_idx, extract @ body_stmts, unique_cond)
          | _ -> None )
        in
        (* Pick the first candidate whose matched constructor has a recursive
           field (skips nullary-reconstruction arms like Nil->Nil that have no
           cell to recycle). *)
        List.find_map try_cand (Escape.find_reuse_candidates typ pv)
      else None
    in
    ( match reuse_stmts_opt with
    | Some (branch_idx, reuse_body, use_count_cond) ->
      let index_cond =
        CPPbinop
          ( Beq,
            mk_call (CPPaccess (Adot, scrut_v, Id.of_string "index")) [],
            CPPint branch_idx )
      in
      let normal = [Smatch (scrut, branches, wildcard)] in
      mk_iife iife_ret_opt
        [Sif (index_cond, [Sif (use_count_cond, reuse_body, normal)], normal)]
    | None ->
      mk_iife iife_ret_opt [Smatch (scrut, branches, wildcard)] )

and gen_cpp_custom_body env k rty ids body scrut_ind_opt =
  let tvars = get_current_type_vars () in
  let ret = cpp_of_ml env rty in
  let ids =
    List.map
      (fun (x, ty) ->
        let ns =
          match scrut_ind_opt with
          | Some g_scrut when not (is_prod_global g_scrut) ->
            (* Use {g_scrut} as the namespace so that type args that are
               self-references of the scrutinee get shared_ptr wrapping —
               matching struct field storage.  Exception 1: when the
               scrutinee is a product/pair (grammar production context),
               fall through to collect_recursive_ns which correctly uses
               the binding variable's own type to find recursive inductives.
               Exception 2: when the binding type IS g_scrut directly (a
               non-parametric direct self-ref dereferenced by the custom
               match template), use empty ns so the binding is a value type
               rather than shared_ptr. *)
            let is_direct_self_ref =
              match ty with
              | Miniml.Tglob (g, [], _) -> GlobRef.CanOrd.equal g g_scrut
              | _ -> false
            in
            if is_direct_self_ref then Refset'.empty
            else Refset'.singleton g_scrut
          | _ -> collect_recursive_ns ty
        in
        (x, convert_ml_type_to_cpp_type env ~ns tvars ty) )
      (List.rev ids)
  in
  (* Wrap erased variables with any_cast when returned as a template parameter. *)
  let k =
    match ret with
    | Tvar _ ->
      let body_is_erased =
        match body with
        | MLrel i ->
          not (binder_is_boxed i) && is_env_var_erased env tvars i
        | Miniml.MLmagic (_, MLrel i) ->
          not (binder_is_boxed i) && is_env_var_erased env tvars i
        | _ -> false
      in
      if body_is_erased then (fun e -> k (Cpp_erasure.unbox ret e))
      else k
    | _ -> k
  in
  let body = gen_stmts env k body in
  (ids, ret, body)

(** Generate a custom case expression using user-provided extraction syntax.
    Entry point for custom pattern match generation.
    Returns a [cpp_stmt list]: when the scrutinee is non-trivial and the
    template uses [%scrut] more than once, a cache declaration
    [auto _cs = expr;] is prepended before the [Scustom_case] node. *)
and gen_custom_cpp_case env k (typ : ml_type) t pv =
  (* Save the ML type for temps computation after fix_a_fired is known. *)
  let ml_typ = typ in
  (* [scrut_is_magic]: true when the scrutinee is erased at runtime (stored as
     [std::any]) even though the ML AST may carry a concrete type annotation.
     Covers both explicit [Obj.magic] wrappers and variables retyped to [Tany]
     by an outer [fix_a_fired] pair match (detected via [env_types]). *)
  let scrut_is_mlmagic = match t with MLmagic (m, _) -> magic_is_boxed env m | _ -> false in
  let scrut_is_cpp_erased = match t with
    | MLrel i -> binder_is_boxed i
    | _ -> false
  in
  let scrut_is_magic = match t with
    | MLmagic (m, _) -> magic_is_boxed env m
    | MLrel i ->
      binder_is_boxed i
      || (match get_env_type_opt i with
          (* An ML type that erases on its own may still have been written
             down concretely here -- a typeclass carrier resolved by the
             instance being generated, say -- in which case the binder holds
             the value itself and there is no box to open. *)
          | Some ty ->
            is_erased_ml_type ty
            && ml_erases_to_box env ty
          | None -> false)
    | _ -> false
  in
  (* [scrut_callee_ret_erased]: the scrutinee is a call to a global function
     ([MLapp (MLglob (r, _), args)], possibly [MLmagic]-wrapped) whose
     DECLARED (un-instantiated) codomain resolves to [std::any] — e.g.
     [rev_tuple : forall xs, syms_semty xs -> syms_semty (rev xs)], a single
     C++ function generic over [xs], so its actual return type is the
     value-dependent-erased [syms_semty] regardless of how a specific
     call-site's Rocq type-checker happened to reduce the annotated result
     type (e.g. to a concrete [prod] when [xs] is a literal list). Using the
     call-site-reduced [typ] alone under-detects this: it looks concrete even
     though the callee only ever returns [std::any] at the C++ level. *)
  let rec flatten_app = function
    | MLapp (f, args) ->
      ( match flatten_app f with
      | MLapp (f', inner_args) -> flatten_app (MLapp (f', inner_args @ args))
      | f' -> MLapp (f', args) )
    | MLmagic (_, e) -> flatten_app e
    | other -> other
  in
  let scrut_callee_ret_erased =
    match flatten_app t with
    | MLapp (MLglob (r, tys), args) ->
      ( match find_type_opt r with
      | Some fty ->
        let fty = match tys with [] -> fty | _ -> Mlutil.type_subst_list tys fty in
        ( match strip_tarr_n (count_real_ml_args args) fty with
        | Some rty ->
          (* Both spellings of "is a [std::any] at run time" are needed here:
             [resolves_to_any_type] follows a named alias for the box, and
             [prints_as_any] catches the codomain a callee left as an erased
             type argument, which converts to a dummy glob rather than to
             [Tany]. *)
          let rty_cpp = cpp_of_ml env rty in
          spells_as_any rty_cpp
        | None -> false )
      | None -> false )
    | _ -> false
  in
  let typ = cpp_of_ml env typ in
  (* [concrete_match_type]: when [typ] is erased ([std::any]), recover the
     actual inductive type from the first branch's pattern constructor and
     its field types.  Used for non-pair matches (e.g. option, variant) where
     we need to emit [any_cast<ConcreteType>(scrut)]. *)
  let concrete_match_type =
    if spells_as_any typ || scrut_callee_ret_erased then
      try
        let _, _, pat0, _ = pv.(0) in
        let ind_ref = match pat0 with
          | Pusual (GlobRef.ConstructRef (ip, _))
          | Pcons (GlobRef.ConstructRef (ip, _), _) -> GlobRef.IndRef ip
          | _ -> raise Not_found
        in
        let ids0, _, _, _ = pv.(0) in
        let tyargs = List.rev_map (fun (_, ty) ->
          erase_unresolved_tvars (cpp_of_ml env ty)
        ) ids0 in
        Tglob (ind_ref, tyargs, [])
      with _ -> typ
    else typ
  in
  (* Custom match templates may use %scrut multiple times (e.g., option: "if
     (%scrut.has_value()) { ... *%scrut; ... }"). Each occurrence re-prints the
     scrutinee C++ expression, so any std::move in the scrutinee would fire
     multiple times. Suppress moves when the template duplicates the
     scrutinee. *)
  let cmatch = find_custom_match pv in
  let scrut_uses =
    List.length
      (List.filter (( = ) Foreign_template.CCscrut) (Foreign_template.match_template cmatch))
  in
  let pair_g_opt_early = match concrete_match_type with
    | Tglob (g, _, _) when is_prod_global g -> Some g
    | _ -> None
  in
  (* [scrut_is_owned_pair]: true when the scrutinee is a pair whose binding
     is dead after destructuring — enables by-value structured binding to move
     the fields out instead of taking a const reference. *)
  let scrut_is_owned_pair = match t with
    | MLrel i | MLmagic (_, MLrel i) ->
      Escape.IntSet.mem i (!tctx).move_owned_vars
      && Array.length pv = 1
      && (let (ids, _, _, body) = pv.(0) in
          let n = List.length ids in
          Escape.nb_occur_match (i + n) body = 0)
    | _ ->
      Array.length pv = 1
      && pair_g_opt_early <> None
  in
  (* Before generating the scrutinee, mark owned vars that are dead after
     the scrutinee (not used in any branch body) so they get std::move.  What
     the enclosing context found dead is dead after the scrutinee only if no
     branch reads it either. *)
  let branch_free =
    Array.fold_left (fun acc (ids, _, _, body) ->
      let n = List.length ids in
      Escape.IntSet.union acc (Escape.free_rels n body))
      Escape.IntSet.empty pv
  in
  let saved_dead = (!tctx).move_dead_after in
  let dead_in_scrut =
    Escape.IntSet.filter (fun i ->
      not (Escape.IntSet.mem i branch_free)
      && Escape.nb_occur_match i t = 1)
      (!tctx).move_owned_vars
  in
  let scrut_is_trivial_ml = match t with
    | MLrel _ | MLmagic (_, MLrel _) -> true
    | _ -> false
  in
  if scrut_uses > 1 && scrut_is_trivial_ml then
    tctx := { !tctx with move_dead_after = Escape.IntSet.empty }
  else
    tctx :=
      { !tctx with
        move_dead_after =
          Escape.IntSet.union
            (Escape.IntSet.diff saved_dead branch_free)
            dead_in_scrut };
  (* A scrutinee whose result is only pinned down by a type index arrives
     boxed, and a match cannot inspect a [std::any].  Telling the call what
     type this position wants is what makes it recover the value. *)
  (* The scrutinee's binder, resolved while [t] is still the ML scrutinee:
     below it is rebound to the generated C++ expression, and inside
     [gen_cases] the name belongs to a branch body. *)
  let scrut_db = scrutinee_binder t in
  let scrut_expected =
    match flatten_app t with
    | MLapp (MLglob (r, _), _)
      when (match find_type_opt r with
            | Some fty -> result_is_index_only_tvar fty
            | None -> false) -> Some typ
    | _ -> None
  in
  (* A scrutinee is not a tail position: whatever the enclosing function
     returns says nothing about the value being matched on.  Naming the
     match's own type here keeps {!position_cpp_ty}'s fallback from recovering a
     boxed scrutinee at the return type -- [any_cast<step_result>] on what is
     a [bool]. *)
  let t =
    let saved_ret = (!tctx).current_cpp_return_type in
    tctx := { !tctx with current_cpp_return_type = Some typ };
    let t = gen_expr ?expected_ty:scrut_expected env t in
    tctx := { !tctx with current_cpp_return_type = saved_ret };
    t
  in
  tctx := { !tctx with move_dead_after = saved_dead };
  let pair_g_opt = match concrete_match_type with
    | Tglob (g, _, _) when is_prod_global g -> Some g
    | _ -> None
  in
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
    let needs_pair_any_cast =
      pair_g_opt <> None &&
      ( scrut_is_cpp_erased || scrut_is_mlmagic || scrut_callee_ret_erased
        || (scrut_is_magic && prints_as_any typ)
        (* Read off the type only where nothing says otherwise: a variable
           is boxed exactly when its binder is ([scrut_is_magic]), and one
           declared [pair<std::any, exp<std::any>>] holds that pair. *)
        || (not scrut_is_trivial_ml)
           && (is_all_erased typ || resolves_to_any_type typ) &&
           ( Ml_type_util.has_tany_in_type concrete_match_type
             || (match concrete_match_type with
                 | Tglob (_, args, _) -> List.exists resolves_to_any_type args
                 | _ -> false) ) )
    in
    if needs_pair_any_cast then begin
      let g = Option.get pair_g_opt in
      (Cpp_erasure.unbox (Tglob (g, [Tany; Tany], [])) (t), true, None)
    end
    else if (scrut_is_mlmagic || (scrut_is_magic && prints_as_any typ)
             || scrut_is_cpp_erased)
            && not (prints_as_any concrete_match_type) then
      (* Erase template args one level deep, preserving nested generic structure.
         E.g., deque<pair<T1,T2>> → deque<pair<any,any>>, deque<T> → deque<any>. *)
      let erase_tparams = function
        | Tglob (_, [], _) -> Tany
        | Tglob (g2, args2, ns2) -> Tglob (g2, List.map (fun _ -> Tany) args2, ns2)
        | _ -> Tany
      in
      (* Canonical erased shape for a LIST scrutinee is [deque<std::any>] -- a
         bare [std::any] per element -- not a structure-preserving
         [deque<pair<any,any>>]: a sibling producer for the same Coq list type
         (e.g. a base-case action erasing an empty list) may already have
         erased to the flat shape, and casting this scrutinee to the
         structure-preserving shape instead would throw [std::bad_any_cast]
         at runtime.  See the matching invariant in [gen_expr]'s
         [MLrel]/[MLmagic] cases. *)
      let cast_ty = match concrete_match_type with
        | Tglob (g, (_ :: _), ns) when is_list_global g ->
          Tglob (g, [Tany], ns)
        | Tglob (g, (_ :: _ as args), ns) when scrut_is_mlmagic ->
          Tglob (g, List.map erase_tparams args, ns)
        | _ -> concrete_match_type
      in
      (Cpp_erasure.unbox cast_ty t, false, Some cast_ty)
    else
      (t, false, None)
  in
  (* When [fix_a_fired], pass [pair<any,any>] as the [Scustom_case] type so
     that {!Cpp_erasure.lower_boxed_reads} reads the scrutinee at
     [pair<any,any>] instead of the concrete nested pair type. *)
  let case_typ =
    if fix_a_fired then
      match pair_g_opt with
      | Some g -> Tglob (g, [Tany; Tany], [])
      | None -> typ
    else
      (* The scrutinee is read at the type it was cast to, which is what a
         template naming its type ([%ty]) has to say. *)
      match cast_to with Some ty -> ty | None -> typ
  in
  (* Compute template type parameters ([%t0], [%t1], ...) after [fix_a_fired]
     is known.  When [fix_a_fired], the scrutinee is cast to [pair<any,any>],
     so all fields are [std::any] regardless of the original field types.
     Force [Tauto] so the binding uses [auto] and C++ deduces the type.
     Also force [Tauto] when a type contains erased positions ([Tany]),
     since an explicit type annotation would block valid concrete-type calls. *)
  let temps =
    match ml_typ with
    | Tglob (_, tys, _) ->
      let raw = template_params_of_ml ~curry:false env tys in
      List.map (fun ty ->
        if fix_a_fired || has_tany_in_type ty then Tauto else ty) raw
    | _ -> []
  in
  (* When the template uses %scrut more than once and the scrutinee is a
     non-trivial expression (function call, constructor, etc.), cache it in
     a temporary to avoid double evaluation. *)
  let scrut, cache_prefix =
    if scrut_uses > 1 && not (is_trivial_scrut t) then begin
      let n = (!tctx).cs_counter in
      tctx := { !tctx with cs_counter = n + 1 };
      let cache_id = Common.scrutinee_cache_id n in
      match lift_iife_assignment cache_id None t with
      | Some stmts -> (CPPvar cache_id, stmts)
      | None -> (CPPvar cache_id, [Sasgn (cache_id, Declare Tauto, t)])
    end else begin
      (t, [])
    end
  in
  (* When the scrutinee is an owned pair (last use), override the template
     with a by-value structured binding to move the fields out. *)
  let binds_by_value = scrut_is_owned_pair && pair_g_opt <> None && not fix_a_fired in
  let cmatch = if binds_by_value then "auto [%b0a0, %b0a1] = %scrut; %br0" else cmatch in
  (* Generate [(params, ret_ty, body)] triples for each branch.  Handles env
     retyping for [fix_a_fired], move tracking for owned pairs, use-site
     [any_cast] insertion, and template-arg stripping for erased arguments. *)
  let alternatives = begin_alternatives () in
  let rec gen_cases = function
    | [] -> []
    | (ids, rty, p, t) :: cs ->
    match p with
    | Pusual r | Pcons (r, _) ->
      enter_alternative alternatives;
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
             ids )
          env
      in
      (* When [fix_a_fired], all pair fields are [std::any] at runtime.
         Variables whose C++ type is a pair (e.g. [pair<any,pair<any,…>>]) are
         also [std::any] — they came from [.second] of a [pair<any,any>].
         Re-type them as [Tany] so that:
         (1) inner pair matches see an erased scrutinee and emit [any_cast],
         (2) {!Cpp_erasure.lower_boxed_reads} treats them as boxed.
         Non-pair leaf types (e.g. [List<any>]) are left unchanged so the
         use-site [any_cast] pass can still insert the correct cast. *)
      let ids' =
        if fix_a_fired then
          List.map (fun (x, ty) ->
            let cpp_ty = cpp_of_ml env ty in
            match cpp_ty with
            | Tglob (g, (_ :: _), _) when is_prod_global g ->
              (x, Tdummy Ktype)
            | Tglob (g, _, _) when is_list_global g ->
              (x, ty)
            | _ when prints_as_any cpp_ty ->
              (x, ty)
            | _ ->
              (x, Tdummy Ktype))
            ids'
        else ids'
      in
      let scrut_elems_are_any =
        (scrut_is_mlmagic || scrut_is_magic)
        && (match ml_typ with
            | Tglob (g, _ :: _, _) when Ml_type_util.is_custom_list_global g -> true
            | _ -> false)
      in
      (* The scrutinee binder's own type, where it is known and says more
         than the case's annotation. *)
      let scrut_ml_typ =
        match scrut_db with
        | Some db -> (
          match get_env_type_opt db with
          | Some t when not (ml_type_contains_erased t) -> t
          | _ -> ml_typ )
        | None -> ml_typ
      in
      let ids' = recover_pattern_var_types_from_scrutinee ~ctor:r scrut_ml_typ ids' in
      let ids' = retype_dependent_params ml_typ ids' in
      let n_pat_vars = List.length ids in
      let saved_env_types = (!tctx).env_types in
      let saved_owned = (!tctx).move_owned_vars in
      push_binders env ids';
      (* When [fix_a_fired] and the outer scrutinee was truly [pair<any,any>]
         at runtime (i.e. outer [typ] was erased, not just magic-wrapped),
         ALL fields are [std::any] at runtime.  Record them as boxed
         so that [gen_expr] emits [any_cast<T>] when they're used at concrete
         types, and so inner pair matches emit [any_cast<pair<any,any>>].
         Use original [ids] types (not the retyped [ids']) to detect field types. *)
      if fix_a_fired then begin
        List.iteri (fun field_i _ ->
          let db_idx = n_pat_vars - field_i in
          record_binder_type db_idx Tany)
          ids
      end;
      let non_erased_def_tys =
        let def_site_field_tys =
          match Table.get_ctor_ip_types_opt r with
          | Some tys -> tys | None -> []
        in
        List.filter (fun t -> not (isTdummy t)) def_site_field_tys
      in
      populate_erased_field_env
        ?scrut_db:
          (Option.map (fun i -> i + n_pat_vars) scrut_db)
        ~cname:r ~typ:ml_typ ~env ~n_pat_vars
        ~n_fields:(List.length ids)
        ~non_erased_def_site_field_tys:non_erased_def_tys ();
      if scrut_elems_are_any then begin
        let n_fields = List.length ids in
        List.iteri (fun field_i _ ->
          let is_self_ref =
            match List.nth_opt non_erased_def_tys field_i with
            | Some (Tglob (g, _, _)) -> is_list_global g
            | _ -> false
          in
          if not is_self_ref then begin
            let db_idx = n_pat_vars - field_i in
            record_binder_type db_idx Tany
          end)
          (List.init n_fields Fun.id)
      end;
      let pat_owned =
        if binds_by_value then
          let ids_rev = List.rev ids in
          List.fold_left (fun acc j ->
            let (_, ty) = List.nth ids_rev j in
            if is_nontrivial_value_ml_type ty
               || Escape.is_shared_ptr_type ty then
              Escape.IntSet.add (j + 1) acc
            else acc)
            Escape.IntSet.empty (List.init n_pat_vars Fun.id)
        else Escape.IntSet.empty
      in
      let scrut_ind_opt =
        match ml_typ with
        | Tglob (GlobRef.IndRef _ as g, _, _) -> Some g
        | _ -> None
      in
      let (br_ids, br_ret, br_stmts) =
        with_shifted_move_tracking n_pat_vars ~add_owned_set:pat_owned (fun () ->
          gen_cpp_custom_body env' k rty ids' t scrut_ind_opt)
      in
      restore_env_types saved_env_types;
      tctx := { !tctx with move_owned_vars = saved_owned };
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
            (fun stmts (name, cpp_ty) ->
               if not (prints_as_any cpp_ty) then
                 let stripped = strip_ns_tglob cpp_ty in
                 let cast_expr =
                   match stripped with
                   | Tglob (g, _, _) when is_prod_global g ->
                     Cpp_erasure.unbox
                       (Tglob (g, [Tany; Tany], []))
                       (CPPvar name)
                   | Tglob (g, [_], _) when is_list_global g && not (Table.is_custom g) ->
                     (* List<T> is stored as List<any> by grammar productions —
                        use the converting constructor List<T>(any_cast<List<any>>(v))
                        so each element is any_cast'd correctly.
                        Preserve any Tnamespace wrapper for correct rendering. *)
                     let list_any_ty =
                       match cpp_ty with
                       | Tnamespace (ns_g, _) ->
                         Tnamespace (ns_g, Tglob (g, [Tany], []))
                       | _ -> Tglob (g, [Tany], [])
                     in
                     Cpp_erasure.converting_ctor cpp_ty
                       [Cpp_erasure.unbox list_any_ty (CPPvar name)]
                   | Tglob (g, [_], _) when Ml_type_util.is_custom_list_global g ->
                     CPPvar name
                   | Tqualified _ | Tglob (GlobRef.ConstRef _, _, _) ->
                     (* Opaque type alias (e.g. nt_semty = std::any) or
                        qualified member type (e.g. typename Ty::sym_semty):
                        the stored value IS the concrete payload, NOT a std::any
                        wrapping it. any_cast<std::any>(any(V)) throws; pass
                        the std::any value as-is. *)
                     CPPvar name
                   | _ -> Cpp_erasure.unbox cpp_ty (CPPvar name)
                 in
                 List.map
                   (local_var_subst_stmt ~keep_cast:true name cast_expr)
                   stmts
               else stmts)
            br_stmts
            br_ids
        else br_stmts
      in
      (* Strip explicit template type args from function calls where any
         argument has erased-type content (either wrapped in [any_cast<T>]
         with [Tany] inside, or a pattern var whose C++ type contains [Tany]).
         Lets C++ deduce the correct type from the argument itself instead of
         using a stale concrete annotation that conflicts with the erased
         runtime type. *)
      let br_stmts =
        let tany_pat_var_names =
          if not fix_a_fired then
            List.fold_left (fun acc (name, cpp_ty) ->
              if has_tany_in_type cpp_ty then Id.Set.add name acc else acc)
              Id.Set.empty br_ids
          else Id.Set.empty
        in
        let should_strip args =
          List.exists (function
            | CPPany_cast (ty, _) -> has_tany_in_type ty
            | CPPvar name -> Id.Set.mem name tany_pat_var_names
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
            List.exists (function Ttyctor _ -> true | _ -> false) tys
          in
          (* Nor can it recover a class instance, which no argument's type
             states -- it is named for that reason -- or a type variable no
             parameter spells, such as one only the result names.  Arguments
             are positional, so only the trailing run deduction can recover is
             given up: the instances that lead the list, and every argument up
             to the last one deduction cannot supply, stay. *)
          let is_instance_arg = function
            | Tvar (Tv_index (_, Some id) | Tv_named id) -> Common.is_tc_instance_id id
            | Tglob (g, _, _) -> ref_is_instance g
            | _ -> false
          in
          let rec instance_prefix = function
            | t :: rest when is_instance_arg t -> t :: instance_prefix rest
            | _ -> []
          in
          let kept_by_deduction r tys =
            let insts = instance_prefix tys in
            let regular = List.filteri (fun i _ -> i >= List.length insts) tys in
            let undeducible =
              match (find_type_opt r, deducible_tvars_of_glob r) with
              | Some ml_ty, Some deducible ->
                let n = IntSet.fold max (collect_tvars_set IntSet.empty ml_ty) 0 in
                let kept =
                  kept_type_arg_positions r n
                in
                if List.length kept <> List.length regular then None
                else Some (List.map (fun i -> not (IntSet.mem i deducible)) kept)
              | _ -> None
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
          let rec fix_expr e = match e with
            | CPPfun_call (res, CPPglob (r, (_ :: _ as tys), ci), args)
              when (not (recovered_carrier tys)) && should_strip (to_reversed args) ->
              CPPfun_call
                (res, CPPglob (r, kept_by_deduction r tys, ci), map_args fix_expr args)
            | _ -> map_expr fix_expr fix_stmt Fun.id e
          and fix_stmt s = map_stmt fix_expr fix_stmt Fun.id s in
          List.map fix_stmt br_stmts
        else br_stmts
      in
      (* Wrap erased pattern variables with any_cast when returned as a template parameter. *)
      let br_stmts =
        match br_ret with
        | Tvar _ ->
          let erased_pat_vars =
            List.fold_left (fun acc (name, cpp_ty) ->
              if prints_as_any cpp_ty then Id.Set.add name acc else acc)
              Id.Set.empty br_ids
          in
          if Id.Set.is_empty erased_pat_vars then br_stmts
          else
            List.map (function
              | Sreturn (Some (CPPvar name))
                when Id.Set.mem name erased_pat_vars ->
                Sreturn (Some (Cpp_erasure.unbox br_ret (CPPvar name)))
              | s -> s)
              br_stmts
        | _ -> br_stmts
      in
      leave_alternative alternatives;
      (br_ids, br_ret, br_stmts) :: gen_cases cs
    | Pwild | Prel _ | Ptuple _ -> gen_cases cs
  in
  let cases = gen_cases (Array.to_list pv) in
  end_alternatives alternatives;
  cache_prefix @
  [ Scustom_case
      ( case_typ,
        scrut,
        temps,
        cases,
        { cm_template = cmatch;
          cm_inductive = Table.indref_of_match pv;
          cm_scrutinee = (if binds_by_value then Scrut_owned else Scrut_borrowed) } ) ]

(** {2 IIFE Inlining}

    When [gen_expr] wraps multi-statement code in an immediately-invoked
    function expression (IIFE):
    {[
      [&]() \{
        unsigned int x = p->px;
        unsigned int y = p->py;
        return (x + y);
      \}()
    ]}
    and the result is consumed at statement level (e.g. by [Sreturn] or
    [Sasgn]), the lambda wrapper is unnecessary.  {!inline_iife} detects
    this pattern and flattens the body statements, replacing the final
    [return] with the enclosing continuation:
    {[
      unsigned int x = p->px;
      unsigned int y = p->py;
      return (x + y);
    ]}
    This produces more readable C++ and avoids interfering with compiler
    optimisations (e.g. copy elision / RVO through a lambda boundary). *)

(** Generate C++ statements from an ML AST. The continuation [k] transforms the
    final expression into a statement (e.g., return, assignment). Handles
    let-bindings, pattern matching, fix expressions, and monadic operations. *)
and gen_stmts ?(slot = empty_slot) env (k : cpp_expr -> cpp_stmt) ast =
  (* Statements open a position of their own and state no type for it: the
     value a [return] here carries goes to the enclosing function, not to the
     position the caller's expression was being built for.  What a tail
     statement lands in is {!with_cpp_return_type}, which
     {!position_cpp_ty} falls back to. *)
  match ast with
  | MLletin (_, _, (MLfix (x, ids, funs, _) as fix_term), b) as _whole ->
    (* Special case for let-fix: the let binding name is the fix function name *)
    (* Resolve unresolved metas in fix function types to Tvars using mgu. *)
    let next_tvar = ref 1 in
    resolve_fix_types ~app_result:ml_app_result_type ~next_tvar ids funs;
    (* Collect all Tvar indices from the fixpoint types *)
    let fix_tvar_indices =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
    in
    let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    (* Check if fixpoint introduces Tvars beyond the outer scope *)
    let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function. Build tvar
         names for all Tvars used in the fixpoint type: - Tvars 1..n_outer reuse
         the outer function's template param names - Tvars beyond n_outer get
         fresh names T<i> *)
      let all_tvar_names = build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
      (* The body being lifted was written against the enclosing declaration's
         class instances -- it spells [typename _tcI0::PTR::ptr] -- and a
         concept-constrained parameter is not an ML type variable, so
         [fix_tvar_indices] cannot mention one.  Carry the head's own
         instances over, ahead of the type variables and explicit at every
         reference: nothing deduces a class instance from an argument. *)
      let class_temps = current_class_temps () in
      let class_args = List.map (fun (_, id) -> named_tvar id) class_temps in
      (* A lifted fix no longer sits inside the scope that bound its free
         variables, so each one becomes a trailing parameter and each call
         grows an argument -- the same closure conversion the lifted-lambda
         path below does.  The names are the outer scope's, so the compiled
         body needs no substitution: only the head and the call sites do. *)
      let free_vars =
        lifted_free_vars ~class_temps env (collect_free_rels 0 fix_term)
      in
      let free_args = List.map (fun (name, _, _) -> CPPvar name) free_vars in
      (* Generate the lifted function name *)
      let fix_name = fst ids.(x) in
      let lifted_ref = lifted_fix_ref fix_name in
      (* Generate the fixpoint body using gen_fix, under the lifted function's
         own tvar scope, passing all mutual fixpoint names *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        with_type_vars all_tvar_names (fun () ->
            Array.to_list
              (Array.mapi
                 (fun i f ->
                   gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i)
                     f )
                 funs ) )
      in
      (* Build a lifted definition for each fixpoint function (usually just one) *)
      let n_fix = Array.length funs in
      List.iteri
        (fun i ((renamed_id, fix_ty), params, body) ->
          let cpp_ty =
            convert_ml_type_to_cpp_type env all_tvar_names fix_ty
          in
          let _, cod =
            match cpp_ty with
            | Tfun (dom, cod) -> (dom, cod)
            | _ -> ([], cpp_ty)
          in
          (* Detect params that are not simply forwarded at recursive call
             sites — these must keep std::function type to avoid infinite
             recursive template instantiation. *)
          let non_fwd_source_indices =
            let lam_params, stripped_body =
              Mlutil.collect_lams funs.(i)
            in
            detect_non_forwarded_params_fix
              (List.length lam_params) n_fix i stripped_body
          in
          let cpp_params, all_temps_with_funs =
            build_lifted_cpp_params
              ~non_fwd_source_indices
              (convert_ml_type_to_cpp_type env all_tvar_names)
              all_temps
              (List.map (fun (n, t, _) -> (n, t)) free_vars @ params)
          in
          (* Replace recursive self-references (CPPvar renamed_n) with calls to
             the lifted function *)
          let rec_call =
            mk_cppglob lifted_ref
              (class_args @ List.map (fun id -> named_tvar id) all_tvar_names)
          in
          let body =
            List.map
              (local_var_subst_stmt ~extra_args:free_args renamed_id rec_call)
              body
          in
          let inner = Dfun (mk_dfun ~ret:cod lifted_ref (Ddef (cpp_params, body))) in
          let lifted_decl =
            Dtemplate (class_temps @ all_temps_with_funs, None, inner)
          in
          add_lifted_decl lifted_decl )
        funs_compiled;
      (* In the continuation body b, the fixpoint name should resolve to a call
         to the lifted function with appropriate type arguments. We push the fix
         name into the env so that MLrel references in b resolve correctly. *)
      let projected_fix_id = (fst ids.(x), snd ids.(x)) in
      let _, env_with_fix = push_vars' [projected_fix_id] env in
      push_binders env [projected_fix_id];
      (* Generate b, then replace references to the fixpoint var with calls to
         the lifted function. Build explicit type args: outer tvars stay as Tvar
         references, extra tvars are resolved to concrete types from the
         enclosing function's return type. *)
      let call_type_args =
        lifted_call_type_args ~class_args ~env ~outer_tvars ~head:None
          ~all_tvar_names ~binder_ty:(snd ids.(0))
          ~param_ml_tys:
            ( match List.nth_opt funs_compiled x with
            | Some (_, params, _) -> List.map snd params
            | None -> [] )
      in
      let lifted_call = mk_cppglob lifted_ref call_type_args in
      (* Phase 2: shift move tracking for the single let binding *)
      let result =
        with_shifted_move_tracking 1 (fun () -> gen_stmts ~slot env_with_fix k b)
      in
      List.map
        (local_var_subst_stmt ~extra_args:free_args fix_name lifted_call)
        result )
    else
      (* No extra Tvars — proceed with local fixpoint approach.

         Three sub-steps:
         1. Compile all mutual fixpoint bodies via {!gen_fix}.
         2. Push only the PROJECTED fixpoint (the one this [MLletin]
            binds) into the continuation environment — not all mutual
            fix names, which would shift de Bruijn indices by [n]
            instead of the correct [1].
         3. Run escape analysis ({!fixpoint_escapes_in_stmts}) on the
            compiled continuation to decide between the [\[&\]] pattern
            ({!gen_local_fix_by_ref}) and the [shared_ptr] pattern
            ({!gen_local_fix_shared_ptr}).

         Move tracking: variables captured by the fixpoint bodies
         ({!Escape.free_rels}) are removed from [move_owned_vars] so
         that [dead_in_a] does not [std::move] them while the fixpoint's
         [\[&\]] lambda still holds references ([fix_move_capture]). *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body) -> (params, body)) funs_compiled
      in
      (* Add only the PROJECTED fixpoint id to the continuation env.
         MLletin binds ONE variable (the projected fixpoint), not all mutual
         fix functions.  Pushing all fix names would shift de Bruijn indices
         by n instead of 1, corrupting references in the continuation.
         However, ALL fix names are added to the avoid set to prevent
         name clashes in subsequent fixpoints (e.g., when the same mutual
         block is instantiated again with a different projection). *)
      let projected_id = List.nth renamed_ids x in
      (* Add non-projected fix names to the avoid set so that subsequent
         fixpoints (e.g., a second MLfix with a different projection from
         the same mutual block) will rename conflicting names. *)
      let env_for_cont =
        let (db, avoid) = env in
        let avoid' = List.fold_left
          (fun acc (i, (id, _)) ->
            if i <> x then Id.Set.add id acc else acc)
          avoid (List.mapi (fun i x -> (i, x)) renamed_ids)
        in
        (db, avoid')
      in
      let _, env_with_fix = push_vars' [projected_id] env_for_cont in
      push_binders env [projected_id];
      (* Compute outer variables captured by the fixpoint bodies.
         If the fixpoint ends up using [&] capture, these variables must
         not be moved in the continuation — the fixpoint holds references
         to them. Even if the fixpoint later uses [=] (escape path),
         suppressing moves is safe (just conservative: copies instead
         of moves for those vars). *)
      let fix_captured =
        Array.fold_left
          (fun acc body ->
            Escape.IntSet.union acc
              (Escape.free_rels (Array.length ids) body))
          Escape.IntSet.empty funs
      in
      (* Shift captured indices: free var at index i in the fix scope
         becomes i+1 in the continuation (one let-binding added). *)
      let captured_shifted =
        Escape.IntSet.map (fun i -> i + 1) fix_captured
      in
      (* Phase 2: shift owned vars and dead-after for the single let binding.
         Remove captured variables from owned set to prevent moves. *)
      let cont =
        with_shifted_move_tracking 1 ~exclude_owned_set:captured_shifted
          (fun () -> gen_stmts ~slot env_with_fix k b)
      in
      (* Check if any fixpoint variable escapes in the continuation.
         If so, use shared_ptr + [=] to prevent dangling references.
         Otherwise, use the simpler [&] capture pattern. *)
      (* Where the fixpoint is used afterwards, and inside its own bodies:
         a self-call in a closure that one of them returns -- a monadic
         [bind]'s continuation -- runs after this scope has gone. *)
      let any_escapes =
        List.exists (fun (id, _) -> fixpoint_escapes_in_stmts id cont) renamed_ids
        || fix_escapes_in_own_bodies renamed_ids funs_with_params
      in
      if any_escapes then
        let decls, defs, deref_subst =
          gen_local_fix_ycomb env renamed_ids funs_with_params
        in
        decls @ defs @ deref_subst cont
      else
        let owned_flags_per_fun =
          Array.to_list (Array.map (fun f ->
            let lam_ids, inner_body = Mlutil.collect_lams f in
            let n_params =
              List.length
                (List.filter
                   (fun (_, ty) -> not (ml_type_is_void ty))
                   lam_ids)
            in
            let n_fix = Array.length funs in
            let all_flags =
              Escape.infer_owned_params (n_params + n_fix) inner_body
            in
            List.init n_params (fun i -> List.nth all_flags i)
          ) funs)
        in
        let decls, defs =
          gen_local_fix_by_ref env renamed_ids funs_with_params
            owned_flags_per_fun
        in
        decls @ defs @ cont
  | MLletin (x, t, (MLlam _ as a), b) ->
    (* Check if this is a polymorphic lambda that should be lifted to a
       top-level template function. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    resolve_metas t;
    resolve_metas_in_ast resolve_metas a;
    (* Collect all Tvar indices from the let-binding type *)
    let tvar_indices = collect_tvars [] t in
    (* Also collect Tvars from the lambda body *)
    let body_tvars = collect_tvars_ast [] a in
    let all_body_tvars = List.sort_uniq Int.compare body_tvars in
    let tvar_indices = List.sort Int.compare tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    let has_extra = List.exists (fun i -> i > n_outer) tvar_indices in
    (* Normal MLletin fallback (shared by no-extra-tvars and
       thunk-with-free-vars cases) *)
    let gen_normal_letin () =
      (* Eta-expand a let-bound lambda whose body returns a function value.
         [convert_ml_type_to_cpp_type] maximally uncurries the binding type,
         so a binding of type [unit -> State bool unit] (= [unit -> (bool ->
         pair)]) becomes [std::function<pair(monostate, bool)>] (2 params) and
         the call site emits a 2-arg call.  But if the RHS is [fun u =>
         state_bind ...] — a 1-binder lambda whose body is itself a [State]
         (a unary function) rather than a nested lambda — the emitted lambda
         only takes 1 arg, so it is not convertible to the 2-param type.  Add
         the missing binders (with types drawn from the arrow structure of [t])
         and apply the body to them, so value, type, and call site all agree on
         arity.  Gated on [n_want > n_have] so fully eta-expanded lambdas (the
         common case) are unchanged. *)
      let a =
        match a with
        | MLlam _ ->
          let n_want = count_ml_value_arrows t in
          let binders, body = collect_lams a in
          let n_have =
            List.length
              (List.filter (fun (_, ty) -> not (Mlutil.isTdummy ty)) binders)
          in
          if n_want <= n_have then
            a
          else
            let rec value_arrow_domains = function
              | Miniml.Tarr (t1, t2) when not (Mlutil.isTdummy t1) ->
                t1 :: value_arrow_domains t2
              | Miniml.Tarr (_, t2) -> value_arrow_domains t2
              | Miniml.Tmeta {contents = Some t} -> value_arrow_domains t
              | _ -> []
            in
            (* Domains of the value-arrows not yet abstracted by the lambda,
               in binding order (outermost first). *)
            let new_doms =
              List.filteri (fun i _ -> i >= n_have) (value_arrow_domains t)
            in
            let d = List.length new_doms in
            if d = 0 then
              a
            else
              (* Use the anonymous binder name so these synthesized params are
                 rendered like every other anonymous lambda parameter (the
                 renamer uniquifies them to [_x0], [_x1], ...) instead of a
                 bespoke [_eta] scheme. *)
              let new_binders =
                List.map (fun dom -> (Id anonymous_name, dom)) new_doms
              in
              (* Args applied to the (lifted) body: the innermost new binder is
                 [MLrel 1], the outermost is [MLrel d]. *)
              let args = List.init d (fun i -> MLrel (d - i)) in
              let lifted_body = ast_lift d body in
              let applied =
                match lifted_body with
                | MLapp (f, xs) -> MLapp (f, xs @ args)
                | _ -> MLapp (lifted_body, args)
              in
              let inner = named_lams (List.rev new_binders) applied in
              named_lams binders inner
        | _ -> a
      in
      let x' = cpp_id_of_id (id_of_mlid x) in
      let renamed_ids, env' = push_vars' [(x', t)] env in
      let x_renamed = fst (List.hd renamed_ids) in
      if x == Dummy then (
        push_binders env [(x_renamed, t)];
        gen_stmts ~slot env' k b )
      else if (!tctx).itree_mode = Reified && is_monadic_ml_type t then begin
        (* Monadic let-binding (reified mode): wrap RHS in an ITree IIFE so
           the variable has type [shared_ptr<ITree<R>>]. *)
        Table.require_itree_header ();
        push_binders env [(x_renamed, t)];
        let r_ml = extract_itree_result_ml t in
        let r_cpp = cpp_of_ml env r_ml in

        let reified_ty = mk_itree_type r_cpp in
        let ret_k v = Sreturn (Some (mk_itree_ret_for_value r_cpp r_ml v)) in
        let body_stmts = gen_stmts env ret_k a in
        let iife = mk_iife (Some reified_ty) body_stmts in
        (* Shift owned vars and dead-after for the continuation *)
        let cont =
          with_shifted_move_tracking 1 (fun () -> gen_stmts ~slot env' k b)
        in
        (* Generate the assignment with reified type *)
        [Sasgn (x_renamed, Declare reified_ty, iife)] @ cont
      end else
        let afun v = Sasgn (x_renamed, Existing, v) in
        let asgn = gen_stmts env afun a in
        (* When the RHS was a pair accessor on an erased argument (e.g.
           snd vs where vs : std::any), the result is std::any at runtime
           even though the ML type says prod(...).  Override to Tdummy so
           downstream pair accessor calls (fst tail) detect erasure. *)
        let t_for_env = if stmts_yield_boxed asgn then Miniml.Tdummy Ktype else t in
        (* Push env_types AFTER generating the value expression [a]. *)
        push_binders env [(x_renamed, t_for_env)];
        (* Phase 2: shift owned vars and dead-after for lambda let binding.
           The body [b] has one more de Bruijn binder, so all indices must
           be shifted +1. *)
        let gen_cont () =
          with_shifted_move_tracking 1 (fun () -> gen_stmts ~slot env' k b)
        in
        match asgn with
        | [Sasgn (_, Existing, e)] ->
          Sasgn
            ( x_renamed,
              Declare (cpp_of_ml env t),
              e )
          :: gen_cont ()
        | _ ->
          Sdecl
            (x_renamed, cpp_of_ml env t)
          :: asgn
          @ gen_cont ()
    in
    if not has_extra then
      gen_normal_letin ()
    else (* Lift the polymorphic lambda to a top-level template function. *)
      let params, body = collect_lams a in
      let n_params = List.length params in
      let x' = cpp_id_of_id (id_of_mlid x) in

      (* 1. Collect free variables in the lambda body *)
      let free_indices = List.sort Int.compare (collect_free_rels n_params body) in

      (* Check if all parameters are dummy/void - if so, this is likely a thunk
         for monadic ops *)
      let all_params_dummy =
        List.for_all (fun (_, ty) -> isTdummy ty || ml_type_is_void ty) params
      in

      if all_params_dummy then
        (* All lambda params are erased type params — this is a polymorphic
           function alias like `let alias := @id`. Don't lift to a top-level
           template; instead inline the lambda into the continuation and
           beta-reduce, so that call sites like `alias nat 9` become direct
           calls like `id(9)`. *)
        let b' = ast_subst a b in
        let rec beta_red_app args = function
          | MLlam (_, _, body) ->
            ( match args with
            | [] -> MLlam (Dummy, Tdummy Ktype, beta_normalize body)
            | _ :: rest -> beta_red_app rest (ast_pop body) )
          | f ->
            let f = beta_normalize f in
            if args = [] then
              f
            else
              MLapp (f, List.map beta_normalize args)
        and beta_normalize = function
          | MLapp ((MLlam _ as f), args) -> beta_red_app args f
          | t -> ast_map beta_normalize t
        in
        let b' = beta_normalize b' in
        gen_stmts ~slot env k b'
      else
        (* 2. Build tvar names: outer tvars keep their names, extra tvars get
           fresh names *)
        let all_tvar_names = build_tvar_names ~outer_tvars tvar_indices in
        let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
        (* The body being lifted was written against the enclosing
           declaration's class instances -- it spells [typename
           _tcI0::PTR::ptr] -- and a concept-constrained parameter is not an
           ML type variable, so [tvar_indices] cannot mention one.  Carry the
           head's own instances over, ahead of the type variables and explicit
           at every reference: nothing deduces a class instance. *)
        let class_temps = current_class_temps () in
        let class_args = List.map (fun (_, id) -> named_tvar id) class_temps in
        let free_vars = lifted_free_vars ~class_temps env free_indices in

        let extended_tvar_names =
          build_extended_tvar_names tvar_indices all_tvar_names all_body_tvars
        in

        (* 3. Generate the lifted function name *)
        let lifted_ref = lifted_fix_ref x' in

        (* 4. Substitution helper for call sites: replace CPPfun_call(CPPvar x',
           args) with CPPfun_call(CPPglob(lifted_ref, []), free_var_cpps @
           args) *)
        (* The lifted function is a template over the binder's type
           arguments, so a parameter declared at one of them is a template
           parameter C++ has to deduce.  A closure has no name to deduce, and
           so cannot agree with the same parameter as settled by another
           argument; {!name_fn_arg_for_tvar_param} names it. *)
        (* {!Mlutil.collect_lams} hands the binders back innermost-first, so
           the source order these are read in is the reverse of [params]. *)
        let param_ml_tys =
          List.rev
            (List.filter_map
               (fun (_, ty) ->
                 if isTdummy ty || ml_type_is_void ty then None else Some ty )
               params )
        in
        let n_actual_params = List.length param_ml_tys in
        (* [args] in source order, as [param_ml_tys] is. *)
        let name_lifted_args args =
          List.mapi
            (fun i a ->
              match List.nth_opt param_ml_tys i with
              | Some ty -> name_fn_arg_for_tvar_param ty a
              | None -> a )
            args
        in
        let rec subst_lifted_call_expr
            (target : Id.t)
            (lifted : cpp_expr)
            (free_args : cpp_expr list)
            (e : cpp_expr) =
          let sub = subst_lifted_call_expr target lifted free_args in
          match e with
          | CPPfun_call (_, CPPvar id, args) when Id.equal id target ->
            (* The lifted template's parameters come from the lambda, so its
               arity is the lambda's. *)
            mk_arity_call
              ~params:(List.map (cpp_of_ml env) param_ml_tys)
              ~saturated:(fun here ->
                CPPfun_call
                  (call_opaque, lifted,
                    of_reversed (free_args @ List.rev (name_lifted_args here)) ) )
              (List.map sub (call_args args))
          | CPPvar id when Id.equal id target ->
            (* Bare reference to lifted function: generate a properly-typed
               wrapper lambda with one parameter per non-erased Rocq lambda
               param. Capture by value ([=]) so that free variables don't
               dangle when the wrapper outlives the current stack frame. *)
            if free_args = [] && n_actual_params = 0 then
              lifted
            else
              let fresh_ids =
                List.init n_actual_params (fun i ->
                  Id.of_string (Printf.sprintf "_xarg%d" i))
              in
              let wrapper_params =
                List.map (fun id -> (Tauto, Some id)) fresh_ids
              in
              let wrapper_call_args =
                free_args @ List.map (fun id -> CPPvar id) fresh_ids
              in
              CPPlambda
                { cl_params = of_reversed wrapper_params;
                cl_tparams = [];
                cl_moved = [];
                  cl_ret = None;
                  cl_body =
                    [ Sreturn
                        (Some
                           (CPPfun_call
                              ( call_opaque, lifted,
                                of_reversed wrapper_call_args ) ) ) ];
                  cl_capture = Closure }
          | CPPany_cast (_, CPPfun_call (_, CPPvar id, args))
            when Id.equal id target ->
            (* The any_cast wraps a direct call to the variable being lifted.
               The lifted template function returns a concrete type (not
               std::any), so drop the cast and replace with the lifted call. *)
            CPPfun_call
              (call_opaque,
                lifted,
                of_reversed (free_args @ List.map sub (to_reversed args)) )
          | CPPany_cast (ty, e') -> Cpp_erasure.unbox ty (sub e')
          | _ ->
            (* Every other form is a plain structural descent.  Spelling the
               cases out by hand is what let uses of [target] under an [if] or
               a [switch] escape rewriting. *)
            map_expr sub (subst_lifted_call_stmt target lifted free_args)
              Fun.id e
        and subst_lifted_call_stmt
            (target : Id.t)
            (lifted : cpp_expr)
            (free_args : cpp_expr list)
            (s : cpp_stmt) =
          map_stmt
            (subst_lifted_call_expr target lifted free_args)
            (subst_lifted_call_stmt target lifted free_args)
            Fun.id s
        in

        (* 6. Compile the lambda body under the extended type-variable
           scope, which numbers the body's Tvars the way the lifted
           function's signature will. *)
        let free_var_params, lam_param_ids, lam_env, compiled_body =
          with_type_vars extended_tvar_names (fun () ->
              (* Push lambda params into env for body compilation *)
              let param_ids =
                List.map
                  (fun (ml_id, ty) -> (cpp_id_of_id (id_of_mlid ml_id), ty))
                  params
              in
              (* For free variables, we need to adjust de Bruijn indices in the body.
                 The body references free vars as MLrel (n_params + i) where i is the
                 outer index. We compile with an env that has: [free_var_params...;
                 lambda_params...] So we push free var names first, then lambda param
                 names. *)
              let free_var_params =
                List.map (fun (name, ty, _) -> (name, ty)) free_vars
              in
              let body_params_for_env = free_var_params @ param_ids in
              let body_param_ids, body_env = push_vars' body_params_for_env env in
              let saved_env_types = (!tctx).env_types in
              push_binders env body_param_ids;

              (* Now compile the body. The body's de Bruijn indices: MLrel 1..n_params
                 -> lambda params (at positions n_free+1..n_free+n_params in our env)
                 MLrel n_params+i -> free var i (should map to position n_free-i+1 in
                 our env, but we actually need to adjust: MLrel (n_params +
                 orig_outer_idx) in the body maps to outer env position
                 orig_outer_idx. In our extended env, free vars are at positions
                 n_params+1..n_params+n_free. So we need to remap. Actually, the body
                 already has correct de Bruijn indices: - MLrel 1..n_params are the
                 lambda params - MLrel (n_params + i) references outer scope position
                 i When we push [free_var_params @ param_ids], the env has: positions
                 1..n_params = param_ids (lambda params) positions
                 n_params+1..n_params+n_free = free_var_params But the body references
                 MLrel(n_params + original_outer_idx), and original_outer_idx may not
                 equal the position in free_var_params. We need the body env to map
                 MLrel(n_params + i) correctly for each free var. *)

              (* Simpler approach: compile body in a modified env where free vars at
                 their original positions are accessible. We push only the lambda
                 params on top of the outer env. *)
              let lam_param_ids, lam_env = push_vars' param_ids env in
              restore_env_types saved_env_types;
              push_binders env lam_param_ids;
              (* The helper is a function of its own: its return type is not
                 the enclosing one's, and nothing in it is owned -- every
                 parameter, captured or not, is declared const by
                 {!build_lifted_cpp_params}.  The enclosing ownership would
                 not even name the same variables, being indexed from outside
                 the lambda's binders. *)
              let compiled_body =
                with_escape_analysis (fun () ->
                    gen_stmts lam_env (fun x -> Sreturn (Some x)) body )
              in
              restore_env_types saved_env_types;
              (free_var_params, lam_param_ids, lam_env, compiled_body) )
        in

        (* 7. Now substitute free variable references in compiled body: Free
           vars in the body were compiled as CPPvar(name_from_outer_env). In the
           lifted function, they become parameters. The names are the same, so
           no substitution of the body is needed — the free var params have the
           same names as the outer scope variables. *)

        (* 8. Build the lifted function parameters: free vars first, then lambda
           params *)
        let all_lifted_params =
          free_var_params
          @ List.filter
              (fun (_, ty) -> (not (ml_type_is_void ty)) && not (isTdummy ty))
              lam_param_ids
        in
        let cpp_params, all_temps_with_funs =
          build_lifted_cpp_params
            (convert_ml_type_to_cpp_type
               lam_env
               extended_tvar_names )
            all_temps
            all_lifted_params
        in

        (* Get return type from the let-binding type *)
        let cpp_ty =
          convert_ml_type_to_cpp_type
            lam_env
            extended_tvar_names
            t
        in
        let cod =
          (* [collect_lams] stops at the first non-lambda, so a let-bound
             [fix] keeps its own binders: the helper takes fewer parameters
             than its type has domains, and what it returns is the closure
             standing for the rest.  A closure type has no spelling, and
             [auto] is how C++ declines to give it one.

             The comparison has to be against the domains that actually took
             a parameter, not the raw arrow count: a domain extraction erased
             (a quantified [Type], a proof) never became one of [params]
             either, so counting it here made an ordinary, fully-applied
             helper with an erased argument -- [fun {A} (x : A) (_ : True) =>
             x], one real binder, two erased ones -- look exactly like a
             curried leftover, and its return type, which is nameable (the
             same [T1] its parameter already spells), fell back to [auto].
             An [auto]-returning template with more than one instantiation in
             the same translation unit is then used before any of them is
             defined. *)
          let ml_dom, _ = Mlutil.type_decomp t in
          let value_dom =
            List.filter (fun d -> not (isTdummy d) && not (ml_type_is_void d)) ml_dom
          in
          if List.length value_dom > n_params then Tauto
          else
            match cpp_ty with
            | Tfun (_, cod) -> cod
            | _ -> cpp_ty
        in

        (* 9. Build and register the lifted declaration.  Call sites below
           name the class prefix and nothing else, so a type parameter whose
           only occurrence is a returned lambda's binder can move into that
           lambda instead of sitting undeducible in the head. *)
        let all_temps_with_funs, compiled_body =
          generalize_lambda_only_tparams all_temps_with_funs cpp_params cod
            compiled_body
        in
        let inner =
          Dfun (mk_dfun ~ret:cod lifted_ref (Ddef (cpp_params, compiled_body)))
        in
        let lifted_decl =
          Dtemplate (class_temps @ all_temps_with_funs, None, inner)
        in
        add_lifted_decl lifted_decl;

        (* 10. Compile the continuation body b, substituting calls to x' with
           calls to the lifted function *)
        let lifted_ids, env' = push_vars' [(x', t)] env in
        let x_lifted = fst (List.hd lifted_ids) in
        push_binders env [(x_lifted, t)];
        (* Phase 2: shift move tracking for lifted lambda binding *)
        let cont =
          with_shifted_move_tracking 1 (fun () -> gen_stmts ~slot env' k b)
        in
        (* Build the free variable argument expressions *)
        let free_var_cpps =
          List.map (fun (name, _, _) -> CPPvar name) free_vars
        in
        (* A lifted lambda's own type variables become template parameters of
           the new top-level function, and one that occurs only in the return
           type is deducible from nothing -- the call has to spell it.  Same
           question, same answer, as the lifted-fix path; but asked of the head
           the declaration ended up with, since generalisation may have moved
           a parameter out of it. *)
        let call_type_args =
          lifted_call_type_args ~class_args ~env ~outer_tvars
            ~head:(Some (List.map snd all_temps_with_funs))
            ~all_tvar_names ~binder_ty:t ~param_ml_tys
        in
        List.map
          (subst_lifted_call_stmt x_lifted
             (mk_cppglob lifted_ref call_type_args)
             free_var_cpps )
          cont
  | MLletin (x, t, a, b) ->
    let x' = cpp_id_of_id (id_of_mlid x) in
    let ids_renamed, env' = push_vars' [(x', t)] env in
    let x_renamed = fst (List.hd ids_renamed) in
    (* The right-hand side is not under the binder, so it keeps [env]'s de
       Bruijn list -- shifting it would misread every index in it.  But
       [x_renamed] is already spoken for by the time the right-hand side runs,
       so a binder the right-hand side introduces has to be freshened against
       it too: [let x := match o with Some x => x end in ...] otherwise names
       the branch binder [x] as well and the assignment reads [x = x].  The
       names come from [env], the avoid set from [env']. *)
    let env_rhs = (fst env, snd env') in
    if x == Dummy then (
      push_binders env [(x_renamed, t)];
      with_shifted_move_tracking 1 (fun () ->
        gen_stmts ~slot env' k b) )
    else if ml_type_is_unit t then (
      (* Unit-typed let bindings: the RHS may call a void-ified function,
         so we can't assign its result to a variable.  Execute the RHS for
         side effects, then declare the variable as Unit::e_TT (its only
         possible value) so the body can still reference it. *)
      push_binders env [(x_renamed, t)];
      let rhs = gen_stmts env_rhs (fun e -> Sexpr e) a in
      (* Drop trivially pure RHS (e.g. Unit::e_TT from tt, variable refs) *)
      let rhs = List.filter (fun s ->
        match s with
        | Sexpr (CPPenum_val _) -> false
        | Sexpr (CPPvar _) -> false
        | _ -> true) rhs in
      (* Generate the body first (under shifted move tracking for the new
         binder), then check if the variable is actually referenced in the
         generated C++ (not just the ML AST, since optimizations like
         unit-match elimination may drop references). *)
      let body =
        with_shifted_move_tracking 1 (fun () -> gen_stmts ~slot env' k b)
      in
      let decl =
        if stmts_reference_var x_renamed body then
          let cpp_ty = cpp_of_ml env t in
          [Sasgn (x_renamed, Declare cpp_ty, mk_tt_expr ())]
        else []
      in
      rhs @ decl @ body )
    else
      let depth = (!tctx).current_letin_depth in
      tctx := { !tctx with current_letin_depth = depth + 1 };
      (* Phase 2: set up dead-after info for move insertion. Compute free vars
         of the continuation [b] (shifted by 1 because [b] is under the let
         binder). A variable at de Bruijn index [i] in [a] is dead-after if
         [i+1] is not free in [b] (since [b] has one extra binder). Only move if
         the variable has exactly 1 occurrence in [a]. *)
      let saved_dead = (!tctx).move_dead_after in
      let saved_owned = (!tctx).move_owned_vars in
      let cont_free = Escape.free_rels 1 b in
      (* free in b, shifted past let binder *)
      let dead_in_a =
        Escape.IntSet.filter
          (fun i ->
            (* i is dead after [a] if i is not free in [b] AND occurs exactly
               once in [a] *)
            (not (Escape.IntSet.mem i cont_free))
            && Escape.nb_occur_match i a = 1 )
          (!tctx).move_owned_vars
      in
      (* Also add any vars from our current dead set that have single occurrence
         in a -- and that [b] does not read: dead after the whole [let] is not
         dead after [a] when the continuation still reads the variable. *)
      let dead_from_above =
        Escape.IntSet.filter
          (fun i ->
            Escape.IntSet.mem i (!tctx).move_dead_after
            && (not (Escape.IntSet.mem i cont_free))
            && Escape.nb_occur_match i a = 1 )
          (!tctx).move_owned_vars
      in
      tctx :=
        { !tctx with
          move_dead_after = Escape.IntSet.union dead_in_a dead_from_above };
      let asgn =
        with_move_suppress_tail true (fun () ->
          (* Single-use partial application optimization: when the RHS is a partial
             application and the bound variable is used at most once in the
             continuation without escaping, AND all free variables of the RHS are
             dead in the continuation (so [&] capture references stay valid),
             tell eta_fun to keep CPPmove wrappers and use [&] capture for
             zero-copy closure generation. *)
          let is_single_use_partial_app =
            match a with
            | MLapp (head, ml_args) | MLmagic (_, MLapp (head, ml_args)) ->
              (match Escape.partial_app_remaining head ml_args with
               | Some remaining ->
                 Escape.nb_occur_match 1 b <= 1
                 && not (Escape.escapes 1 b)
                 && Escape.IntSet.is_empty
                      (Escape.IntSet.inter (Escape.free_rels 0 a) cont_free)
                 && Escape.single_use_nargs 1 b >= remaining
               | None -> false)
            | _ -> false
          in
          let afun v = Sasgn (x_renamed, Existing, v) in
          (* Thread the let-binding's type annotation as the expected ML type
             so that gen_ctor_call can recover the concrete element type for
             constructors (like nil) whose ML annotation has unresolved metas or
             erased type args.  For example: let sk = [] : list parser_frame — the
             let-binding knows the element type even when the nil's own annotation
             has Tdummy Ktype. *)
          (* Look ahead: if t has erased type args, look at the body b to see if the
             bound var (MLrel 1 in b) is used as the i-th arg of a constructor call
             with a non-erased corresponding type arg. If so, use that type instead of t.
             This recovers the correct element type for nils bound before pair constructors:
               let empty_stack : list(Tmeta) = [] in make_pair(fr, empty_stack)
             where the pair type says the second arg is list(parser_frame). *)
          let t_effective =
            let t_has_erased = ml_type_contains_erased t in
            if not t_has_erased then t
            else begin
              (* Try to infer from an MLcons that immediately follows in the body.
                 The body b may be directly an MLcons, or wrapped in one more MLletin. *)
              let try_cons_body (b_inner : Miniml.ml_ast) db_offset =
                (* db_offset: how many let-bindings above b_inner, so MLrel (1+db_offset) = x *)
                let target_rel = 1 + db_offset in
                (* Resolve t to get the underlying inductive (through metas) *)
                let t_ind_opt = match resolve_tmeta t with
                  | Miniml.Tglob (t_ind, _, _) -> Some t_ind
                  | _ -> None
                in
                match b_inner with
                | Miniml.MLcons (ctor_ty, _, ts) ->
                  let result = ref None in
                  List.iteri (fun i (ti : Miniml.ml_ast) ->
                    match ti with
                    | Miniml.MLrel r when r = target_rel ->
                      (match resolve_tmeta ctor_ty with
                       | Miniml.Tglob (_, ctor_tys, _) ->
                         (match List.nth_opt ctor_tys i with
                          | Some raw_candidate ->
                            (match resolve_tmeta raw_candidate with
                            | Miniml.Tglob (ind, sub_tys, _) as candidate ->
                              (* Check that candidate's inductive matches t's inductive.
                                 When t is fully erased (Tmeta{None}), accept any concrete type. *)
                              let matches_t = match t_ind_opt with
                                | Some t_ind -> GlobRef.CanOrd.equal ind t_ind
                                | None -> true
                              in
                              if matches_t && not (List.exists is_erased_ml_type sub_tys) then
                                result := Some candidate
                            | _ -> ())
                          | _ -> ())
                       | _ -> ())
                    | _ -> ()
                  ) ts;
                  !result
                | _ -> None
              in
              (* Try to infer t from an MLapp body: find the position of target_rel
                 in the application args, look up the function's ML type, and extract
                 the type of that arg.  This handles the pattern:
                   let sk0 : Tmeta = (fr, nil) in multistep(..., sk0, ...)
                 where multistep's type tells us sk0 has type parser_frame × list(parser_frame). *)
              let try_app_body (b_inner : Miniml.ml_ast) db_offset =
                let target_rel = 1 + db_offset in
                match b_inner with
                | Miniml.MLapp (Miniml.MLglob (func_ref, _), app_args)
                | Miniml.MLapp (Miniml.MLmagic (_, Miniml.MLglob (func_ref, _)), app_args) ->
                  let rec find_pos args i =
                    match args with
                    | [] -> None
                    | (Miniml.MLrel r) :: _ when r = target_rel -> Some i
                    | (Miniml.MLmagic (_, Miniml.MLrel r)) :: _ when r = target_rel -> Some i
                    | _ :: rest -> find_pos rest (i + 1)
                  in
                  (match find_pos app_args 0 with
                  | None -> None
                  | Some idx ->
                    (match find_type_opt func_ref with
                    | None -> None
                    | Some func_ty ->
                      let rec nth_arg ty n =
                        match ty with
                        | Miniml.Tarr (Miniml.Tdummy _, cod) -> nth_arg cod n
                        | Miniml.Tarr (dom, _) when n = 0 -> Some dom
                        | Miniml.Tarr (_, cod) -> nth_arg cod (n - 1)
                        | Miniml.Tmeta {contents = Some t2} -> nth_arg t2 n
                        | _ -> None
                      in
                      let try_unfold_typedef resolved =
                        match resolved with
                        | Miniml.Tglob (GlobRef.ConstRef kn, _, _) ->
                          (match Table.lookup_typedef_unchecked kn with
                           | Some expanded -> expanded
                           | None -> resolved)
                        | _ -> resolved
                      in
                      (match nth_arg func_ty idx with
                      | Some arg_ty ->
                        let resolved = resolve_tmeta arg_ty in
                        let resolved = try_unfold_typedef resolved in
                        (match resolve_tmeta t, resolved with
                        | _, Miniml.Tglob (_, r_sub, _)
                          when not (List.exists is_erased_ml_type r_sub) ->
                          Some resolved
                        | _ -> None)
                      | None -> None)))
                | _ -> None
              in
              let inferred = match (b : Miniml.ml_ast) with
                | Miniml.MLcons _ -> try_cons_body b 0
                | Miniml.MLletin (_, _, a', _) ->
                  (* In body = MLletin(sk0, pair_expr, ...), nil is at MLrel 1 in pair_expr.
                     db_offset=0 because pair_expr is evaluated before sk0 is bound. *)
                  (match try_cons_body a' 0 with
                   | Some _ as r -> r
                   | None -> try_cons_body b 0)
                | Miniml.MLapp _ ->
                  (* Body is a function application — look up the function type to find
                     the type expected for the bound variable at its argument position. *)
                  try_app_body b 0
                | _ -> None
              in
              match inferred with Some ty -> ty | None -> t
            end
          in
          (* The bound value is not the enclosing function's result, so the
             result a position falls back to when it states nothing is the
             binder's own type, where it says one: [let t := x <- arg ;; ...]
             is a tree over [arg]'s family, whatever family the function
             returns into. *)
          let rhs_result =
            if ml_type_contains_erased t_effective then (!tctx).current_cpp_return_type
            else
              let c = cpp_of_ml env t_effective in
              match spell_in_scope c with
              | Some _ as t -> t
              | None -> (!tctx).current_cpp_return_type
          in
          with_cpp_return_type rhs_result (fun () ->
            gen_stmts
              ~slot:
                { slot with
                  deep_erase = false;
                  expected_ml_ty = Some t_effective;
                  eta_keep_moves = is_single_use_partial_app }
              env_rhs afun a ) )
      in
      (* Push env_types AFTER generating the value expression [a] — [a] uses de
         Bruijn indices that don't include the new let binding.  The body [b]
         (generated below) does include it. *)
      let t_for_env = if stmts_yield_boxed asgn then Miniml.Tdummy Ktype else t in
      push_binders env [(x_renamed, t_for_env)];
      (* Shift saved_dead +1 for the body [b]: the new let binding adds one
         de Bruijn level, so all parent-scope indices must be shifted to stay
         in sync with the body's coordinate system. *)
      tctx :=
        { !tctx with
          move_dead_after = Escape.IntSet.map (fun i -> i + 1) saved_dead };
      (* The new let binding is owned (it's a local variable). Update
         move_owned_vars for processing [b]: shift all existing indices by 1
         (because [b] has one more binder) and add index 1 if the type is
         shared_ptr. *)
      let shifted_owned =
        Escape.IntSet.map (fun i -> i + 1) (!tctx).move_owned_vars
      in
      (* Const-ref binding optimisation: when the RHS [a] is a record-field
         access (single-branch MLcase) on a source variable that is NOT being
         moved at this point, we can bind the result as [const T&] instead of
         [T].  This avoids an unnecessary shared_ptr refcount increment at the
         binding site; any subsequent owned uses still copy from the reference.

         A variable k is moved only when it is in BOTH [move_owned_vars] (owned
         value semantics) AND [move_dead_after] (last use at this point).  When
         the source has further uses in the let body it will not be moved, so
         the const-ref remains valid.  We only apply this when the type is a
         shared_ptr so that primitive types (int, bool) are left unchanged. *)
      let use_const_ref =
        Escape.is_shared_ptr_type t
        &&
        ( match a with
          | MLcase (_, MLrel k, pv)
            when Array.length pv = 1
                 && (match pv.(0) with (_, _, _, MLrel _) -> true | _ -> false)
                 && not (Escape.IntSet.mem k (!tctx).move_owned_vars
                         && Escape.IntSet.mem k (!tctx).move_dead_after) ->
            true
          | _ -> false )
      in
      let new_is_tracked =
        (Escape.is_shared_ptr_type t || is_nontrivial_value_ml_type t)
        && not use_const_ref
      in
      let owned_for_b =
        if new_is_tracked then
          Escape.IntSet.add 1 shifted_owned
        else
          shifted_owned
      in
      tctx := { !tctx with move_owned_vars = owned_for_b };
      let result =
        match asgn with
          | [Sasgn (_, Existing, e)] ->
            let cpp_ty = cpp_of_ml env t in
            (* When the type contains Tany (from erased carrier projections) but
               the generated expression is a lambda with concrete types, derive
               the std::function type from the lambda's parameter and return
               types. *)
            let cpp_ty =
              match (cpp_ty, e) with
              | Tfun (dom, _), CPPlambda
                { cl_params = params;
                  cl_ret = Some ret_ty;
                  _ }
                when List.exists has_tany_in_type dom ->
                let strip_tmod = function
                  | Tconst t -> t
                  | t -> t
                in
                let param_tys =
                  List.rev_map (fun (ty, _) -> strip_tmod ty) (to_reversed params)
                in
                Tfun (param_tys, ret_ty)
              | _, CPPlambda _ -> cpp_ty
              | _, _
                when has_erased_type_in_type cpp_ty
                     || Ml_type_util.has_unresolved_promoted_in_type cpp_ty ->
                (* Type contains erased positions (Tany or dummy_type marker)
                   but the expression is not a lambda with inferable types.
                   Use [auto] so the C++ compiler deduces the concrete type
                   from the RHS — e.g. for pair-projection bindings like
                   [const auto &prs = tup.first] where the erased type would
                   be [List<pair<String, any>>] but the actual type of
                   [tup.first] is [List<pair<String, JV>>], or for existT nil
                   constructors where the element type is dummy_type. *)
                Tauto
              | _ -> cpp_ty
            in
            (* Apply const-ref binding when safe. *)
            let cpp_ty =
              if use_const_ref then Tref (Lvalue, Tconst cpp_ty)
              else cpp_ty
            in
            begin match extract_block_template e with
            | Some (ref, tmpl, args, tys) ->
              Sblock_custom (ref, tmpl, x_renamed, cpp_ty, args, tys)
              :: gen_stmts ~slot env' k b
            | None ->
              Sasgn (x_renamed, Declare cpp_ty, e) :: gen_stmts ~slot env' k b
            end
          | _ ->
            let cpp_ty = cpp_of_ml env t in
            (Sdecl (x_renamed, cpp_ty) :: asgn) @ gen_stmts ~slot env' k b
      in
      tctx := { !tctx with move_owned_vars = saved_owned };
      result
  | MLapp (MLfix (x, ids, funs, _), args) ->
    (* Resolve unresolved metas in fix function types to Tvars using mgu.
       Traverse types and assign Tvar 1, 2, ... to each unresolved meta. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    resolve_fix_types ~app_result:ml_app_result_type ~next_tvar ids funs;
    Array.iter (resolve_metas_in_ast resolve_metas) funs;
    List.iter (resolve_metas_in_ast resolve_metas) args;
    (* Collect Tvars from bodies too *)
    let body_tvars = Array.fold_left collect_tvars_ast [] funs in
    let all_body_tvars = List.sort_uniq Int.compare body_tvars in
    (* Collect all Tvar indices from the fixpoint types *)
    let fix_tvar_indices =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
    in
    let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    (* Check if fixpoint introduces Tvars beyond the outer scope *)
    let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function *)
      let all_tvar_names = build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
      (* The body being lifted was written against the enclosing declaration's
         class instances -- it spells [typename _tcI0::PTR::ptr] -- and a
         concept-constrained parameter is not an ML type variable, so
         [fix_tvar_indices] cannot mention one.  Carry the head's own
         instances over, ahead of the type variables and explicit at every
         reference: nothing deduces a class instance from an argument. *)
      let class_temps = current_class_temps () in
      let class_args = List.map (fun (_, id) -> named_tvar id) class_temps in
      let extended_tvar_names =
        build_extended_tvar_names fix_tvar_indices all_tvar_names all_body_tvars
      in
      let fix_name = fst ids.(x) in
      let lifted_ref = lifted_fix_ref fix_name in
      (* Compile under the lifted function's extended tvar scope, which covers
         both signature and body Tvar indices. *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        with_type_vars extended_tvar_names (fun () ->
            Array.to_list
              (Array.mapi
                 (fun i f ->
                   gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i)
                     f )
                 funs ) )
      in
      (* Build lifted declarations *)
      let n_fix = Array.length funs in
      List.iteri
        (fun i ((renamed_id, fix_ty), params, body) ->
          let cpp_ty =
            convert_ml_type_to_cpp_type
              env
              extended_tvar_names
              fix_ty
          in
          let _, cod =
            match cpp_ty with
            | Tfun (dom, cod) -> (dom, cod)
            | _ -> ([], cpp_ty)
          in
          let non_fwd_source_indices =
            let lam_params, stripped_body =
              Mlutil.collect_lams funs.(i)
            in
            detect_non_forwarded_params_fix
              (List.length lam_params) n_fix i stripped_body
          in
          let cpp_params, all_temps_with_funs =
            build_lifted_cpp_params
              ~non_fwd_source_indices
              (convert_ml_type_to_cpp_type
                 env
                 extended_tvar_names )
              all_temps
              params
          in
          let rec_call =
            mk_cppglob lifted_ref
              (class_args @ List.map (fun id -> named_tvar id) all_tvar_names)
          in
          let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
          let inner = Dfun (mk_dfun ~ret:cod lifted_ref (Ddef (cpp_params, body))) in
          let lifted_decl =
            Dtemplate (class_temps @ all_temps_with_funs, None, inner)
          in
          add_lifted_decl lifted_decl )
        funs_compiled;
      (* Generate args in outer scope and call the lifted function. Build
         explicit type args: outer tvars stay as Tvar references, extra tvars
         are resolved to concrete types from the enclosing context. Extra tvars
         that appear as the fixpoint's return type are resolved to the enclosing
         function's C++ return type (current_cpp_return_type). *)
      let call_type_args =
        class_args
        @
        let extra_tvar_names =
          List.filter
            (fun id -> not (List.exists (Id.equal id) outer_tvars))
            all_tvar_names
        in
        if extra_tvar_names = [] then
          (* All tvars are outer — C++ can deduce them *)
          []
        else
          (* Get the fixpoint's template return type to identify which extra
             tvar it uses *)
          let fix_ty = snd ids.(x) in
          let tmpl_cpp_ty =
            convert_ml_type_to_cpp_type
              env
              extended_tvar_names
              fix_ty
          in
          let tmpl_cod =
            match tmpl_cpp_ty with
            | Tfun (_, cod) -> cod
            | t -> t
          in
          let outer_args = List.map (fun id -> named_tvar id) outer_tvars in
          let tvar_map =
            match (!tctx).current_cpp_return_type with
            | Some conc_ret -> extract_tvar_map tmpl_cod conc_ret
            | None -> []
          in
          let extra_args =
            List.map
              (fun tvar_name ->
                match List.find_opt
                        (fun (id, _) -> Id.equal id tvar_name)
                        tvar_map with
                | Some (_, ty) -> ty
                | None ->
                  match (!tctx).current_cpp_return_type with
                  | Some ret_ty -> ret_ty
                  | None -> named_tvar tvar_name )
              extra_tvar_names
          in
          outer_args @ extra_args
      in
      let cpp_args = List.rev_map (gen_expr env) args in
      [k (CPPfun_call (call_opaque, mk_cppglob lifted_ref call_type_args, of_reversed cpp_args))] )
    else (* No extra Tvars - proceed with by-ref local fixpoint (immediately applied) *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body) -> (params, body)) funs_compiled
      in
      let args = List.rev_map (gen_expr env) args in
      let _, fix_params, _ = List.nth funs_compiled x in
      let n_provided = List.length args in
      let n_fix_params = List.length fix_params in
      if n_provided < n_fix_params then begin
        (* Partial application: the fixpoint escapes (returned as a lambda).
           Use Y-combinator pattern so the fixpoint body doesn't capture
           a stack-local std::function by reference. *)
        let decls, defs, deref_subst =
          gen_local_fix_ycomb env renamed_ids funs_with_params
        in
        let remaining_params =
          (* [fix_params] is in de Bruijn order -- last parameter first -- so
             the arguments already supplied fill its tail, not its head.  What
             is left over is the front of the list, returned in source order
             so the wrapper's parameters line up with the call below. *)
          List.rev (safe_firstn (n_fix_params - n_provided) fix_params)
        in
        let pa_params =
          List.mapi
            (fun j (_, ml_ty) ->
              let cpp_ty =
                cpp_of_ml env ml_ty
              in
              (cpp_ty, Some (Id.of_string (Printf.sprintf "_pa%d" j))) )
            remaining_params
        in
        let pa_exprs =
          List.map (fun (_, id_opt) -> CPPvar (Option.get id_opt)) pa_params
        in
        let fix_id = fst (List.nth renamed_ids x) in
        let full_call = mk_call (CPPvar fix_id) (args @ pa_exprs) in
        decls @ defs
        @ deref_subst [k (mk_lambda pa_params None [Sreturn (Some full_call)] ~capture:Closure)]
      end else if fix_escapes_in_own_bodies renamed_ids funs_with_params then
        let decls, defs, deref_subst =
          gen_local_fix_ycomb env renamed_ids funs_with_params
        in
        decls @ defs
        @ deref_subst
            [k (CPPfun_call (call_opaque, CPPvar (fst (List.nth renamed_ids x)), of_reversed args))]
      else begin
        let owned_flags_per_fun =
          Array.to_list (Array.map (fun f ->
            let lam_ids, inner_body = Mlutil.collect_lams f in
            let n_params =
              List.length
                (List.filter
                   (fun (_, ty) -> not (ml_type_is_void ty))
                   lam_ids)
            in
            let n_fix = Array.length funs in
            let all_flags =
              Escape.infer_owned_params (n_params + n_fix) inner_body
            in
            List.init n_params (fun i -> List.nth all_flags i)
          ) funs)
        in
        let decls, defs =
          gen_local_fix_by_ref env renamed_ids funs_with_params
            owned_flags_per_fun
        in
        decls @ defs
        @ [k (CPPfun_call (call_opaque, CPPvar (fst (List.nth renamed_ids x)), of_reversed args))]
      end
  | MLfix (x, ids, funs, _) ->
    (* Standalone fixpoint (not immediately applied) — e.g., appearing as the
       RHS of a let-binding.  Since the fixpoint value itself is returned (not
       called in place), it will always escape.  Use the Y-combinator pattern:
       the generated wrapper lambda [fix_name] is already a plain callable. *)
    let next_tvar = ref 1 in
    resolve_fix_types ~app_result:ml_app_result_type ~next_tvar ids funs;
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled =
      Array.to_list
        (Array.mapi
           (fun i f ->
             gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
           funs )
    in
    let renamed_ids =
      List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
    in
    let funs_with_params =
      List.map (fun (_, params, body) -> (params, body)) funs_compiled
    in
    let decls, defs, _deref_subst =
      gen_local_fix_ycomb env renamed_ids funs_with_params
    in
    let fix_id = fst (List.nth renamed_ids x) in
    decls @ defs @ [k (CPPvar fix_id)]
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h -> gen_stmts env k
     (MLapp (a1, a2::[])) *)
  | MLapp (MLglob (r, bind_tys), a1 :: a2 :: l) when is_bind r ->
    (* Reified mode: bind is a real function call, not desugared. *)
    if (!tctx).itree_mode = Reified then
      let saved_dead = (!tctx).move_dead_after in
      let e = gen_tail_expr ~slot env ast in
      let result = inline_iife k e in
      tctx := { !tctx with move_dead_after = saved_dead };
      result
    else begin
      (* Sequential mode: desugar bind into sequential statements. *)
      let a_ml, f = Common.last_two (a1 :: a2 :: l) in
      let a = gen_expr env a_ml in
      let ids', f = collect_lams f in
    (* Resolve metas in continuation parameter types using bind's type
       arguments. bind has type forall A B, IO A -> (A -> IO B) -> IO B. The
       first type argument is A, which is the type of the continuation
       parameter. Use mgu to unify them, which mutably resolves metas. Skip
       Tdummy entries in bind_tys — these come from failed type extractions in
       make_tyargs (e.g., HKT type constructors that can't be extracted).
       Unifying a meta with Tdummy would not resolve it usefully. *)
    let non_dummy_bind_tys = filter_value_types bind_tys in
    let () =
      match non_dummy_bind_tys with
      | elem_ty :: _ -> List.iter (fun (_, ty) -> try_mgu ty elem_ty) ids'
      | [] -> ()
    in
    let ids, env =
      push_vars'
        (List.map (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty)) ids')
        env
    in
    push_binders env ids;
    (* The continuation's lambda parameter adds one de Bruijn level.
       Shift move tracking sets so that parent-scope owned-variable indices
       stay in sync with the body's coordinate system.  Without this shift,
       after N bind continuations the indices drift by N, causing spurious
       collisions that produce incorrect std::move (use-after-move). *)
    let add_owned =
      match ids with
      | (_, ty) :: _ when Escape.is_shared_ptr_type ty
                          || is_nontrivial_value_ml_type ty -> Some 1
      | _ -> None
    in
    with_shifted_move_tracking 1 ?add_owned (fun () ->
    match ids with
    | (x, ml_ty) :: _ ->
      let ty = cpp_of_ml env ml_ty in
      if ty == Tvoid || ty == Tunresolved || ml_type_is_unit ml_ty then
        (* Unit/void bind result: execute the action for side effects,
           then declare the variable as Unit::e_TT so the continuation
           can reference it if needed. *)
        let action_is_pure_ret =
          match a_ml with
          | MLapp (MLglob (r, _), _) when is_ret r -> true
          | _ -> false
        in
        let side_effect =
          match a with
          | CPPenum_val _ -> []
          | _ when action_is_pure_ret -> []
          | _ -> [Sexpr a]
        in
        (* Generate the continuation first, then check if the variable is
           actually referenced in the generated C++ (unit-match elimination
           and Ret-in-void optimization may drop ML-level references). *)
        let body = gen_stmts ~slot env k f in
        let cpp_ty = cpp_of_ml env ml_ty in
        let decl =
          if not (stmts_reference_var x body) then []
          else if ml_type_is_unit ml_ty && not (is_cpp_unit_type cpp_ty) then
            []
          else if ml_type_is_unit ml_ty then
            [Sasgn (x, Declare cpp_ty, mk_tt_expr ())]
          else
            []
        in
        side_effect @ decl @ body
      else begin
        match extract_block_template a with
        | Some (ref, tmpl, args, tys) ->
          Sblock_custom (ref, tmpl, x, ty, args, tys)
          :: gen_stmts ~slot env k f
        | None ->
          Sasgn (x, Declare ty, a) :: gen_stmts ~slot env k f
      end
    | _ ->
      (* No lambda parameters (eta-reduced continuation like bare Ret).
         Execute the action for side effects, then run the continuation. *)
      let side_effect =
        match a with CPPenum_val _ -> [] | _ -> [Sexpr a]
      in
      ( match f with
      | MLglob (r, _) when is_ret r ->
        (* Eta-reduced Ret: bind action Ret = action (monad right identity).
           In sequential mode, just execute the action and return. *)
        if (!tctx).current_cpp_return_type = Some Tvoid then
          side_effect @ [Sreturn None]
        else
          [k a]
      | _ ->
        (* Eta-reduced non-Ret continuation: f is a bare function reference.
           Bind action result to a temp var and apply f to it, instead of
           discarding the result and returning f unapplied. *)
        let non_void_ty =
          match non_dummy_bind_tys with
          | ty :: _ ->
            let cpp_ty =
              cpp_of_ml env ty
            in
            if cpp_ty = Tvoid || cpp_ty = Tunresolved || ml_type_is_unit ty then
              None
            else
              Some cpp_ty
          | [] -> None
        in
        ( match non_void_ty with
        | Some cpp_ty ->
          let temp_id = Id.of_string "_bind_result" in
          let f_expr = gen_expr env f in
          let app = mk_call f_expr [CPPvar temp_id] in
          [Sasgn (temp_id, Declare cpp_ty, a); k app]
        | None ->
          side_effect @ gen_stmts ~slot env k f ) ) )
    end
  | MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
    if (!tctx).itree_mode = Reified then begin
      (* Reified mode: Ret is a constructor call, not desugared. *)
      let saved_dead = (!tctx).move_dead_after in
      let e = gen_tail_expr ~slot env ast in
      let result = inline_iife k e in
      tctx := { !tctx with move_dead_after = saved_dead };
      result
    end
    else begin
      (* Sequential mode: eliminate Ret, just use the value. *)
      let t = Common.last (a1 :: l) in
      if (!tctx).current_cpp_return_type = Some Tvoid then
        (* Void-returning function: discard the value and return. *)
        [Sreturn None]
      else
        [k (gen_expr ?expected_ty:(position_cpp_ty None) env t)]
    end
  | MLcase (typ, t, pv) when is_custom_match pv ->
    (* Set up dead-after for owned variables at their last use, same as the
       default tail-position case below. Without this, owned variables
       passed as function arguments in the scrutinee would not get std::move.
       Suppress when processing a let-binding RHS to avoid use-after-move. *)
    let saved_dead = (!tctx).move_dead_after in
    ( if not (!tctx).move_suppress_tail then
        let tail_dead =
          Escape.IntSet.filter
            (fun i -> Escape.nb_occur_match i ast = 1)
            (!tctx).move_owned_vars
        in
        tctx :=
          { !tctx with
            move_dead_after =
                Escape.IntSet.union (!tctx).move_dead_after tail_dead } );
    let result = gen_custom_cpp_case env k typ t pv in
    tctx := { !tctx with move_dead_after = saved_dead };
    result
  | MLcons (_, r, []) when Table.is_tt_constructor r
      && (!tctx).current_cpp_return_type = Some Tvoid ->
    (* tt (unit constructor) in tail position of a void-returning function *)
    if (!tctx).itree_mode = Reified then begin
      Table.require_itree_header ();
      [k (mk_itree_ret Tvoid [])]
    end
    else
      [Sreturn None]
  | MLglob (r, _) when is_ghost r ->
    if (!tctx).itree_mode = Reified then begin
      (* Reified mode: ghost (void value) at tail position must produce
         ITree<void>::ret() rather than bare return, since the function
         returns shared_ptr<ITree<void>>. *)
      Table.require_itree_header ();
      [k (mk_itree_ret Tvoid [])]
    end
    else
      [Sreturn None]
  | MLexn msg ->
    (* Generate throw statement for unreachable/absurd cases (e.g., empty
       match) *)
    [Sthrow msg]
  | MLmagic (_, MLexn msg) ->
    (* Handle MLexn wrapped in MLmagic *)
    [Sthrow msg]
  | MLcase (typ, t, pv)
    when (not (record_fields_of_type typ == [])) && Array.length pv == 1 ->
    let ids, _r, _pat, body = pv.(0) in
    let n = List.length ids in
    let body' = match body with MLmagic (_, b) -> b | b -> b in
    let is_simple =
      match body' with
      | MLrel i when i <= n -> true
      | MLapp (MLrel i, _) when i <= n -> true
      | MLapp (MLmagic (_, MLrel i), _) when i <= n -> true
      | _ -> false
    in
    if is_simple then
      (* Simple body: gen_expr handles these as direct field access (no IIFE),
         so delegate to the default path. *)
      let saved_dead = (!tctx).move_dead_after in
      ( if not (!tctx).move_suppress_tail then
          let tail_dead =
            Escape.IntSet.filter
              (fun i -> Escape.nb_occur_match i ast = 1)
              (!tctx).move_owned_vars
          in
          tctx :=
            { !tctx with
              move_dead_after =
                  Escape.IntSet.union (!tctx).move_dead_after tail_dead } );
      let value =
        gen_expr ?expected_ty:(position_cpp_ty None) env ast
      in
      (* A function value returned into an erased ([std::any]) return type --
         e.g. the [nat -> nat] branch of a dependent [if ... then nat else
         nat -> nat] -- must be stored in the canonical adapter form the
         application site casts back to. *)
      let value =
        match (!tctx).current_cpp_return_type with
        | Some ret_ty when resolves_to_any_type ret_ty ->
          erase_fn_for_any_slot ast value
        | _ -> value
      in
      let result = inline_iife k value in
      tctx := { !tctx with move_dead_after = saved_dead };
      result
    else
      (* Complex body: emit field extraction assignments as flat statements
         instead of wrapping in an IIFE. This produces clean code for all
         continuations (return, assignment, etc.). *)
      let is_typeclass = Table.is_typeclass_type typ in
      let all_fields = record_fields_of_type typ in
      let non_erased_fields = List.filter_map Fun.id all_fields in
      let make_field_access base_expr fld =
        if is_typeclass then
          let fld_name = Common.id_of_global Term fld in
          CPPscope (base_expr, fld_name, [])
        else
          CPPget' (base_expr, fld, record_field_cpp_ty env typ fld)
      in
      let renamed_ids, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
             ids )
          env
      in
      let renamed_ids_fwd = List.rev renamed_ids in
      let tvars = get_current_type_vars () in
      let asgns =
        List.concat_map
          (fun (i, ((renamed_name, _), (_, ty))) ->
            let fld =
              try Some (List.nth non_erased_fields i) with _ -> None
            in
            let e =
              match fld with
              | Some fld -> make_field_access (gen_expr env t) fld
              | _ ->
                CErrors.anomaly (Pp.str "record field index out of bounds")
            in
            let e =
              match typ with
              | Tglob (record_ref, _, _) ->
                let storage_ty =
                  convert_ml_type_to_cpp_type env ~ns:(Refset'.singleton record_ref)
                    tvars
                    ty
                in
                let api_ty =
                  cpp_of_ml env ty
                in
                wrap_api_expr ~storage_ty ~api_ty e
              | _ -> e
            in
            let api_ty_for_decl =
              cpp_of_ml env ty
            in
            let decl_ty =
              if has_tany_in_type api_ty_for_decl then
                Tref (Lvalue, Tconst Tauto)
              else
                api_ty_for_decl
            in
            match lift_iife_assignment renamed_name (Some decl_ty) e with
            | Some stmts -> stmts
            | None -> [Sasgn (renamed_name, Declare decl_ty, e)])
          (List.mapi (fun i x -> (i, x)) (List.combine renamed_ids_fwd ids))
      in
      let env_ids =
        List.map
          (fun ((n, _), (_, ty)) -> (n, ty))
          (List.combine renamed_ids_fwd ids)
        |> retype_dependent_params typ
      in
      push_binders env env_ids;
      asgns @ gen_stmts ~slot env' k body
  | t ->
    (* Tail position: generate expression with dead-after tracking.
       No deref_reified needed: in sequential mode, monadic variables are
       direct values (bind desugars to let-binding); in reified mode,
       they are trees returned as-is. *)
    let saved_dead = (!tctx).move_dead_after in
    let is_void_tail = match t with
      | MLapp (f, args) | MLmagic (_, MLapp (f, args)) ->
        ml_callee_is_void f
        (* Only treat as void if fully applied — partial applications
           return a function value, not void. *)
        && ( match f with
           | MLglob (r, _) ->
             ( match find_type_opt r with
             | Some ty ->
               let rec count_arrows = function
                 | Miniml.Tarr (t1, rest) ->
                   if isTdummy t1 then count_arrows rest
                   else 1 + count_arrows rest
                 | _ -> 0
               in
               let n_non_dummy_args =
                 List.length (List.filter (fun a ->
                   match a with MLdummy _ -> false | _ -> true) args)
               in
               n_non_dummy_args >= count_arrows ty
             | None -> true )
           | _ -> true )
      | _ -> false
    in
    if is_void_tail then begin
      let e =
        gen_tail_expr ~slot ?expected_ty:(position_cpp_ty None) env t
      in
      tctx := { !tctx with move_dead_after = saved_dead };
      if (!tctx).current_cpp_return_type = Some Tvoid then
        [Sexpr e; Sreturn None]
      else
        match k (CPPint 0) with
        | Sexpr _ ->
          (* Side-effect-only continuation (e.g. from unit let handler).
             The void call provides the side effect; the caller handles
             the variable declaration separately.  No value needed. *)
          [Sexpr e]
        | _ ->
          [Sexpr e] @ inline_iife k (mk_tt_expr ())
    end
    else begin
      (* Whether this continuation is the function's result rather than a
         binding.  Probing [k] is how the void case above already asks. *)
      let k_returns = match k (CPPint 0) with Sreturn _ -> true | _ -> false in
      let e =
        gen_tail_expr ~slot ?expected_ty:(position_cpp_ty None) env t
      in
      (* A pair accessor applied to an erased pair yields a [std::any] at run
         time even though its ML type is concrete.  In tail position that value
         is the result, so cast it back to the declared return type -- the same
         recovery the let-binding path performs by marking the bound variable
         erased. *)
      let e =
        match (!tctx).current_cpp_return_type with
        | Some rt when k_returns -> recover_boxed_component rt e
        | _ -> e
      in
      let result = inline_iife k e in
      tctx := { !tctx with move_dead_after = saved_dead };
      result
    end

(** Generate a C++ expression for [t] in tail position.
    Marks owned variables that occur exactly once as dead-after (for
    last-use move semantics).  Callers are responsible for saving and
    restoring [move_dead_after].

    Used by the default tail case and by reified-mode bind/ret handlers
    (which bypass monadic desugaring and treat bind/Ret as plain calls). *)
and gen_tail_expr ?expected_ty ?(slot = empty_slot) env t =
  ( if not (!tctx).move_suppress_tail then
      let tail_dead =
        Escape.IntSet.filter
          (fun i -> Escape.nb_occur_match i t = 1)
          (!tctx).move_owned_vars
      in
      tctx :=
        { !tctx with
          move_dead_after =
              Escape.IntSet.union (!tctx).move_dead_after tail_dead } );
  gen_expr ?expected_ty ~slot env t

(** Generate a fixpoint (recursive function) definition. Handles both single and
    mutually recursive functions. [all_fix_ids] contains names of all mutual
    fixpoints; [fix_idx] is the index of this fixpoint in the mutual group. *)
and gen_fix env ?(all_fix_ids = []) ~fix_idx (n, ty) f =
  let ids, f = collect_lams f in
  let ids, _ =
    push_vars'
      (List.map (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty)) ids)
      env
  in
  (* Push all mutual fixpoint names (or just (n,ty) for single fixpoints). For
     mutual fixpoints, all_fix_ids contains all fixpoint names in array order.
     For single fixpoints, all_fix_ids is empty and we use [(n,ty)].

     IMPORTANT: Rocq's extraction pushes fix bindings so that the LAST function
     is at db 1 and the FIRST is at db n (standard de Bruijn convention with
     fold_left over the array). We must reverse fix_names to match. *)
  let fix_names = if all_fix_ids = [] then [(n, ty)] else all_fix_ids in
  let n_fix_funs = List.length fix_names in
  let fix_names_db_order = List.rev fix_names in
  let renamed_fix_ids, env = push_vars' (ids @ fix_names_db_order) env in
  let saved_env_types = (!tctx).env_types in
  push_binders env (ids @ fix_names_db_order);
  (* Extract the renamed name for THIS fixpoint function. fix_names_db_order
     is reversed from the array order, so fix array index i corresponds to
     position (n_fix_funs - 1 - i) in the reversed list. *)
  let n_lam_params = List.length ids in
  let renamed_n =
    fst (List.nth renamed_fix_ids
           (n_lam_params + (n_fix_funs - 1 - fix_idx))) in
  let ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) ids in
  (* Phase 2: set up move state for fixpoint body. Fix params are owned (passed
     by value in the generated std::function lambda). After push_vars'(ids @
     fix_names), de Bruijn indices in f are: ids[0] → db 1, ..., ids[k-1] → db
     k, fix_names[0] → db k+1, ..., fix_names[m-1] → db k+m. We only mark lambda
     params as owned (not the fix self-references). *)
  let saved_dead = (!tctx).move_dead_after in
  let saved_owned = (!tctx).move_owned_vars in
  let saved_nparams = (!tctx).move_n_params in
  let n_fix_params = List.length ids in
  let n_total = n_fix_params + n_fix_funs in
  let fix_owned_base = Escape.infer_owned_params n_total f in
  let fix_sub_esc = Escape.infer_sub_bindings_escape_params n_total f in
  tctx :=
    { !tctx with
      move_owned_vars =
          List.fold_left
            (fun acc i ->
              let db = i + 1 in
              let base_owned =
                match List.nth_opt fix_owned_base i with
                | Some b -> b
                | None -> false
              in
              let sub_esc =
                match List.nth_opt fix_sub_esc i with
                | Some b -> b
                | None -> false
              in
              let ml_ty = snd (List.nth ids i) in
              let owned = base_owned
                || (sub_esc && is_prod_ml_type ml_ty) in
              if owned && (Escape.is_shared_ptr_type ml_ty
                           || is_nontrivial_value_ml_type ml_ty) then
                Escape.IntSet.add db acc
              else
                acc )
            Escape.IntSet.empty
            (List.init n_fix_params (fun i -> i)) };
  tctx := { !tctx with move_dead_after = Escape.IntSet.empty };
  tctx := { !tctx with move_n_params = n_fix_params + n_fix_funs };
  let result =
    ((renamed_n, ty), ids, gen_stmts env (fun x -> Sreturn (Some x)) f)
  in
  restore_env_types saved_env_types;
  tctx := { !tctx with move_dead_after = saved_dead };
  tctx := { !tctx with move_owned_vars = saved_owned };
  tctx := { !tctx with move_n_params = saved_nparams };
  result

let () = type_term_arg := fun env a -> gen_expr env a

(** Whether [expr] is a numeral-converter application (e.g.
    [Nat.of_num_uint (Number.UIntDecimal ...)]) that {!gen_expr} folds into a
    literal via [Table.get_numeral_info].  When true, the whole subtree is
    replaced by a raw integer literal at translation time, so the converter and
    its digit-chain argument (and everything they transitively reference) are
    never emitted.  Dependency collection uses this to avoid pulling in the
    vestigial [of_num_uint]/[of_uint]/[Uint] machinery. *)
let is_foldable_numeral_converter_app = function
  | MLapp (MLglob (r, _), [arg]) when Table.is_numeral_converter r ->
    ( match try_fold_num_uint arg with
    | Some _ -> true
    | None -> Option.has_some (try_fold_num_int arg) )
  | _ -> false

(** [with_method_ns_for_locals () f] runs [f] with the module's local
    inductives added to {!Translation_state.method_self_ns}, and puts the
    enclosing namespace back on the way out however [f] leaves.

    Functions inside wrapper modules (e.g. Cotree.tree_of_cotree) construct
    containers whose type parameters must use shared_ptr for recursive
    value-type inductives, matching struct field types.

    @param base  The namespace to extend, when the caller has one of its own in
      hand.  Defaults to the ambient {!Translation_state.method_self_ns}. *)
let with_method_ns_for_locals ?base (f : unit -> 'a) : 'a =
  let full_ns =
    List.fold_left
      (fun acc g ->
        if Table.has_recursive_fields g && not (is_enum_inductive g)
        then Refset'.add g acc
        else acc)
      (Option.default (!tctx).method_self_ns base)
      (get_local_inductives ())
  in
  with_method_self_ns full_ns f

(** Adapt closures returned from a function whose return type is the erased
    [std::any] (e.g. the [nat -> nat] branch of a dependent
    [if b then nat else nat -> nat]).  Like {!erase_fn_for_any_slot} at
    argument and value-declaration positions, the callable must be stored in
    the canonical [std::function<std::any(std::any...)>] form that the
    application site recovers with an [any_cast].  Nested lambda bodies are
    left alone: their returns answer to their own return type. *)
let erase_returned_fn_values (ret_ty : cpp_type) (body : cpp_stmt list) =
  if not (resolves_to_any_type ret_ty) then body
  else
    let rec fix_stmt s =
      match s with
      | Sreturn (Some (CPPlambda _ as e)) ->
        Sreturn (Some (wrap_crane_erase_fn e))
      | _ -> map_stmt Fun.id fix_stmt Fun.id s
    in
    List.map fix_stmt body

(** [return_type_is_erased param_vars ret] -- [ret], the return type of a method
    on an inductive whose kept parameters are [param_vars], has no C++ spelling
    and must be rendered as [std::any].

    This is the judgement {!Method_registry.create} asks for.  It lives here
    because it is a question about C++ types, and the registry is deliberately
    kept below the type translation. *)
let return_type_is_erased (param_vars : Id.t list) (ret : ml_type) : bool =
  type_is_erased
    (convert_ml_type_to_cpp_type (empty_env ()) param_vars ret)
