(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Constructor applications and the values they store: a constructor's
    factory call or aggregate, a custom constructor's template, and each
    argument generated against the field it fills ({!gen_stored_value}).  One of the modules lowering Core
    bodies to CppIR that {!Translation} drives; it calls back into
    expression and statement lowering through {!Translation_knot}. *)

open Base.Common
open Names
open Base.Table
open Util
open Translation_state
open Base.Type_util
open Core_plan.Query
open Translation_constructors
open Translation_knot
open Translation_lambda
open Translation_application

(** The name a hoisted constant is declared under (see {!Cpp_constants}): a
   numeral's value where the term is one of Rocq's [positive], [N], [Z] or
   [nat] -- [pos_10], [z_neg_5], [pos] past twenty digits -- and [k]
   otherwise. *)
let constant_name e =
  let ind_name = function
    | GlobRef.ConstructRef ((kn, _), j) -> Some (Label.to_string (MutInd.label kn), j)
    | _ -> None
  in
  let rec pos = function
    | Core.Expr.Construct {constructor = r; arguments = args; _} -> (
      match (ind_name r, args) with
      | Some ("positive", 1), [p] -> Option.map (fun v -> Z.(add (mul v (of_int 2)) one)) (pos p)
      | Some ("positive", 2), [p] -> Option.map (fun v -> Z.mul v (Z.of_int 2)) (pos p)
      | Some ("positive", 3), [] -> Some Z.one
      | _ -> None )
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> pos a
    | _ -> None
  in
  let rec nat = function
    | Core.Expr.Construct {constructor = r; arguments = args; _} -> (
      match (ind_name r, args) with
      | Some ("nat", 1), [] -> Some Z.zero
      | Some ("nat", 2), [n] -> Option.map Z.succ (nat n)
      | _ -> None )
    | _ -> None
  in
  (* A numeral too long to read is named by its kind alone. *)
  let named prefix v =
    let digits = Z.to_string v in
    Some (if String.length digits <= 20 then prefix ^ digits else String.sub prefix 0 (String.length prefix - 1))
  in
  let name =
    match e with
    | Core.Expr.Construct {constructor = r; arguments = args; _} -> (
      match (ind_name r, args) with
      | Some ("positive", _), _ -> Option.bind (pos e) (named "pos_")
      | Some ("N", 2), [p] -> Option.bind (pos p) (named "n_")
      | Some ("Z", 2), [p] -> Option.bind (pos p) (named "z_")
      | Some ("Z", 3), [p] -> Option.bind (pos p) (named "z_neg_")
      | Some ("nat", _), _ -> Option.bind (nat e) (named "nat_")
      | _ -> None )
    | _ -> None
  in
  Option.default "k" name

(** A value a constructor stores: an argument of a constructor or a custom
    constructor, or a record's field.  An erased proof or type there --
    [{| unwrap := nat |}] at [wrap Set] -- is the empty box its erased slot
    takes, not the throw a dead position gets, since the constructor runs as
    the value is built; a call returning [unit] is the value its void call
    stands for. *)
let gen_stored_value cx ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~slot env e : Cpp_ir.Lowered.Expr.t =
  match e with
  | Core.Expr.Erased_value _ -> Cpp_erasure.empty_box
  | e when Translation_monadic.core_value_is_void_call cx e ->
    Translation_monadic.wrap_void_call_as_value (gen_expr cx ~slot env e)
  | _ -> gen_expr cx ?expected_ty ~slot env e

(** The constructor [r] of a custom-extracted inductive at [ty] applied to
    [ts]: the user's constructor template instantiated at the type arguments
    the slot and annotation agree on, each argument generated against the
    field it fills and boxed where that field is erased (never for a
    pass-through constructor such as ["%a0"], which has no field storage),
    and an identity template collapsed to its one argument. *)
let gen_expr_custom_cons cx ?(expected_ty : Cpp_ir.Lowered.Type.t option) ?(slot = Translation_slot.empty_slot) env
    (ty : Core.Type.t) r ts : Cpp_ir.Lowered.Expr.t =
  let slot = into_erased_return cx slot in
  let ty = custom_refined_annotation cx env ~expected_ty ~slot ty r ts in
  (* Some custom-extracted inductives (e.g. [sum1], registered as
     [Crane Extract Inductive sum1 => "" ["%a0" "%a0"]]) are pure type-level
     erasure markers: their constructor template forwards the argument
     completely unboxed, with no runtime wrapper type at all. For these, the
     generic "erase Core.Type.Variable-typed fields into std::any" logic below must NOT
     fire, because there is no field storage to box into — the value must
     stay exactly as it was produced. Wrapping it anyway makes the erased
     [std::any] hold the argument's own (possibly unique closure) type
     instead of whatever a downstream consumer expects inside that [std::any]
     (e.g. [itree_vis] expects [std::function<std::any()>], not a bare
     lambda), and the mismatched [std::any_cast] throws at runtime
     (CWE-704, finding 44). *)
  let is_passthrough_ctor_arg = Translation_ctor_args.ctor_arg_is_passthrough r in
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
     NOT in [promoted_var_map]) fall back to [Any] = [std::any].

     We do NOT clear [promoted_var_map] here: inside template functions,
     promoted vars must resolve to qualified types (e.g., typename _tcI0::Obj)
     so that constructor type args match the function's declared return type.
     At module level, [promoted_var_map] is already empty, so the
     [in_constructor_expr] fallback handles it naturally. *)
  (* Inside a polymorphic function object the erased type the Core annotation
     withheld is the lambda's own template parameter, so a type-argument list
     erasure left empty says the carrier rather than printing [std::any] for a
     value the parameter has already pinned down.  See {!Rank2}. *)
  let type_args_at_carrier r =
    match get_rank2_carrier cx with
    | Some x -> Option.default [] (Rank2.type_args_at_carrier x r)
    | None -> []
  in
  let result =
    with_in_constructor_expr cx true @@ fun () ->
  (* Convert value arguments to C++ expressions.  An erased proof or type
     argument ([Core.Expr.Erased_value]) is the empty box its erased slot takes; see that
     case of {!gen_expr}. *)
  let gen_ctor_arg ?expected_ty ?(slot = slot) e =
    gen_stored_value cx ?expected_ty ~slot env e
  in
  let c = custom cx env ~expected_ty ~slot ty r in
  let ty_args_for_expected = c.ty_args_for_expected and field_types_for_wrap = c.field_types in
  let ctor_temps_at_slot = c.temps_at_slot and slot_states_unboxed = c.states_unboxed in
  let is_list_cons_ctor = c.list_cons and slot_is_deeply_erased = c.deeply_erased in
  let args =
    List.rev (List.mapi (fun i e ->
      let a = custom_field cx env c ~slot r i e in
      let e = a.term and new_expected = a.expected_core and erased_fn_slot = a.erased_fn_slot in
      let result =
        with_cpp_return_type cx a.ret (fun () -> gen_ctor_arg ?expected_ty:a.expected ~slot:a.slot e)
      in

      (* Where this argument is stored, as far as its representation goes:
         [Some [Any]] when the slot is erased and the value has to be boxed
         into it, [None] when it is stored as itself. *)
      let field_slot =
        (* A pass-through constructor (registered as ["%a0"]) has no field
           storage at all -- the argument is forwarded verbatim, so there is
           nothing to box into. *)
        if is_passthrough_ctor_arg i then None
        else
          match List.nth_opt field_types_for_wrap i with
          | Some (Core.Type.Variable {variable = j; _}) ->
            ( match List.nth_opt ctor_temps_at_slot (j - 1) with
              (* The slot's real type may be a value-dependent erased type's
                 own alias (e.g. [pred_ty = crane::obj]) rather than the bare
                 [Any] node, so unfold it before comparing -- otherwise a
                 function value stored there is never boxed at all, and the
                 declaration's constraint on the callable (still stated
                 against its concrete, un-erased signature) never gets
                 dropped either. *)
              | Some t when Cpp_ir.Types.prints_as_any (Translation_types.unfold_cpp_typedef cx env t) ->
                ( match result with
                  (* A lambda that is not a function value is a generated IIFE,
                     not a callable being stored. *)
                  | Lambda _ when not (Translation_erasure.core_expr_is_function_value cx e) -> None
                  | _ -> Some Cpp_ir.Type.Any )
              (* A slot that kept a concrete result but erased its domain
                 ([std::function<uint64_t(std::any)>], a pair component whose
                 Rocq type is [sty -> nat] at an erased [sty]) is not a box:
                 a callable reaches it through the [crane_erase_fn] adapter,
                 which {!Translation_coerce.coerce} supplies once it is told the slot's own
                 signature. *)
              | Some _ when erased_fn_slot <> None -> erased_fn_slot
              | Some _
                when slot_is_deeply_erased && not (slot_states_unboxed (j - 1))
                ->
                Some Cpp_ir.Type.Any
              | _ -> None )
          | _ -> None
      in
      let into =
        match field_slot with
        | Some _ as slot -> slot
        | None when Translation_slot.boxed slot ->
          (* This constructor names a concrete type for the field, so there is
             no erased slot to box into: the custom C++ form consumes the
             argument at that type.  [Ascii] is the clearest case -- its eight
             [bool] arguments are folded into a [static_cast<char>] bitmask, and
             a [std::any] is not contextually convertible to [bool].  A
             recursive field ([Core.Type.Global_app] naming the constructor's own inductive) is
             the same situation. *)
          let field_is_concrete =
            match List.nth_opt field_types_for_wrap i with
            | Some (Core.Type.Global_app _ as ft) ->
              not (Cpp_ir.Types.prints_as_any (Translation_types.cpp_of_core cx env ft))
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
            | Some core_fty ->
              ( match Translation_types.cpp_of_core cx env core_fty with
                | Entity_application (_, _ :: _, _) -> true
                | _ -> false )
            | None -> false
          in
          if field_is_concrete || is_already_container then None else Some Cpp_ir.Type.Any
        | None -> None
      in
      let result =
        match into with
        | Some into -> Translation_coerce.coerce cx ~term:e ~into result
        | None -> result
      in
      result) ts)
  in
  (* Helper to wrap expression in function call syntax if it has arguments.
     [yields] is the constructed value's C++ type, where the caller could work
     it out: a custom constructor is still a value of its inductive, so
     recording it here is what lets a consumer -- a loopification frame field,
     say -- name the type instead of falling back on [decltype]. *)
  let app ?yields x : Cpp_ir.Lowered.Expr.t =
    match args with
    | [] -> x
    | _ ->
      Call
        (Cpp_ir.Build.signature ?yields ~nargs:(List.length args) (), x,
         List.rev args)
  in
  (* When [ty] (the Core.Expr.Construct node's own type annotation) is not itself a
     resolved [Core.Type.Global_app] — e.g. an open annotation ([Core.Type.Open]), which
     happens for a "cons" expression built from destructured pattern
     variables whose types extraction failed to unify with a non-reducible
     dependent computation (see [recover_pattern_var_types_from_scrutinee])
     — fall back to [ty_args_for_expected], already computed above via
     [deep_resolve]/[expected_core_ty] for the very same
     purpose (recovering nil's element type in a pair).  Without this, a
     "cons" production whose own return type stayed unresolved loses its
     [list] template argument entirely, so [cpp_print.ml] can't substitute
     the generic [cons : A -> list A -> list A] schema's [Core.Type.Variable]s and
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
    | Core.Type.Global_app {head = n; type_arguments = tys; index_arguments = sc}
      when List.length ty_args_for_expected = List.length tys
           && List.exists (core_type_contains_erased ~in_arrows:true) tys ->
      Core.Type.Global_app {head = n; type_arguments = ty_args_for_expected; index_arguments = sc}
    | Core.Type.Global_app _ -> ty
    | _ when ty_args_for_expected <> [] ->
      ( match r with
      | GlobRef.ConstructRef ((kn, i), _) ->
        Core.Type.Global_app {head = GlobRef.IndRef (kn, i);
                              type_arguments = ty_args_for_expected;
                              index_arguments = []}
      | _ -> ty )
    | _ -> ty
  in
  let result =
    match ty with
    | Core.Type.Global_app {head = n; type_arguments = tys; _} ->
      (* Step 1: Filter out index type args - only keep parameters.

         Inductive types distinguish between parameters (uniform across all
         constructors, e.g., the [A] in [list A]) and indices (may vary,
         e.g., the [n] in [vec A n]). In C++, only parameters become template
         arguments; indices are encoded in types or runtime values.

         We use [get_ind_num_param_vars_opt] to find the parameter count and
         [safe_firstn] to extract them. [safe_firstn] handles cases where the
         use wrote fewer type arguments than the parameters (a partial
         application). *)
      let tys =
        match n with
        | GlobRef.IndRef (kn, _) ->
          ( match Base.Table.get_ind_num_param_vars_opt kn with
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
      (* Step 2: Convert Core types to C++ types.  The enclosing type-variable
         names matter: inside a member template a [Core.Type.Variable] is one of the
         method's own parameters ([_A0]), not an anonymous [T2].  The
         arguments instantiate an {i inductive's} parameters, so a stored
         function type keeps the flat arity its declaration is written at
         ([~site:Declared]); currying here would make the instantiation
         disagree with the type the declaration spells. *)
      let temps = Translation_types.template_params_of_core cx ~site:Cpp_ir.Types.Declared env tys in
      let temps = filter_erased_type_args temps in
      let temps = Translation_types.ind_promoted_type_args cx n @ temps in
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
            match slot.Translation_slot.expected_core_ty with
            | Some (Core.Type.Global_app {head = exp_r; type_arguments = exp_tys; _})
              when Names.GlobRef.CanOrd.equal exp_r n
                   && List.length exp_tys = List.length tys ->
              let exp_temps = Translation_types.build_template_params cx ~site:Cpp_ir.Types.Through_tvar env []
                exp_tys in
              let r = filter_erased_type_args exp_temps in
              if r <> [] && not (List.exists (function Cpp_ir.Type.Variable (Index (_, None)) -> true | _ -> false) r)
              then r
              else []
            | _ -> []
          in
          if from_expected <> [] then from_expected
          else
            let from_ret =
              match current_cpp_return_type cx () with
              | Some (Cpp_ir.Type.Entity_application (ret_r, ret_tys, _))
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length tys ->
                filter_erased_type_args ret_tys
              | Some (Cpp_ir.Type.Shared_pointer (Entity_application (ret_r, ret_tys, _)))
                when Names.GlobRef.CanOrd.equal n ret_r
                     && List.length ret_tys = List.length tys ->
                filter_erased_type_args ret_tys
              | _ -> []
            in
            if from_ret <> [] then from_ret
            else if cx.ctx.lexical.promoted_var_map <> [] then
              Option.default temps (Translation_ctor_args.promoted_tys_of_arity cx (List.length tys))
            else temps
        else temps
      in
      (* For custom list constructors (e.g., deque nil/cons), a container
         element type built entirely from [Core.Type.Erased] placeholders (extraction's
         "no information available" marker, e.g. because the production's
         return type is an opaque, non-reducible alias like [symbol_semty])
         carries no genuine field information.  A sibling production for the
         SAME Coq list type may still see concrete structure here (e.g. a
         literal, directly-annotated [list (string*nat)]); preserving that
         structure as [pair<any,any>] while the other production collapses
         to bare [std::any] would produce two incompatible container shapes
         for the same runtime list, causing an [any_cast] mismatch at the
         consumer.  Collapse to bare [std::any] whenever the container is
         hollow, whether or not its slot is [Boxed], so nil/cons always
         agree on representation. *)
      let is_custom_list =
        match r with
        | GlobRef.ConstructRef ((kn, _), _) ->
          let ind = GlobRef.IndRef (kn, 0) in
          Base.Type_util.is_custom_list_global ind
        | _ -> false
      in
      let rec core_ty_all_dummy = function
        | Core.Type.Erased _ -> true
        | Core.Type.Global_app {type_arguments = (_ :: _ as args); _} -> List.for_all core_ty_all_dummy args
        | Core.Type.Meta {contents = Some t} -> core_ty_all_dummy t
        | _ -> false
      in
      (* [hollow_container] fires when the list's Core element annotation is all
         [Core.Type.Erased] (extraction couldn't reduce it, e.g. an opaque alias like
         [symbol_semty]).  Collapsing to bare [std::any] is only correct when
         the concrete C++ element type ([temps]) is ITSELF erased — i.e. a
         sibling production for the same erased list would build [deque<any>]
         and the two must agree.  When [temps] recovers a fully-concrete
         element type despite the hollow Core annotation (e.g. an abstract
         [frame] seen through a module type, which still resolves to the
         concrete [typename D::Defs::frame]), the list is a genuine
         [deque<frame>] flowing into a concretely-typed consumer, so the
         concrete element type must be preserved. *)
      let hollow_container =
        is_custom_list && List.exists core_ty_all_dummy tys
        && List.exists Base.Type_util.has_erased_type_in_type temps
      in
      let temps =
        if hollow_container && temps <> [] then
          List.map (fun _ -> Cpp_ir.Type.Any) temps
        else if Translation_slot.boxed slot && temps <> [] then
          (* Canonical erased shape for a list is [deque<std::any>] -- a bare
             [std::any] per element, not a structure-preserving
             [deque<pair<any,any>>].  A sibling production for the same Coq
             list type (e.g. one built via a different code path that already
             collapses to the flat shape) must agree exactly, or the
             consumer's [any_cast] throws [std::bad_any_cast] at runtime.
             See the matching invariant in [gen_expr]'s [Core.Expr.Bound_variable]/[Core.Expr.Coerce]
             cases. *)
          List.map (fun _ -> Cpp_ir.Type.Any) temps
        else temps
      in
      let temps = if temps = [] then type_args_at_carrier n else temps in
      let value_ty = Cpp_ir.Type.Entity_application (n, temps, []) in
      app ~yields:value_ty (mk_cppglob ~yields:value_ty r temps)
    | _ ->
      (* Type is not a Core.Type.Global_app - no type args to pass.
         This case is rare for custom constructors, which typically have
         Core.Type.Global_app types. Fall back to bare constructor reference. *)
      app (mk_cppglob r (type_args_at_carrier r))
  in
  result
  in
  (* Collapse identity inline customs (%a0) for constructors, matching
     the same collapse done for function applications at gen_expr. *)
  let result =
    match result with
    | Call (_, Entity (_, _, Some ci), [single_arg])
      when Option.map (fun (t : Cpp_ir.Foreign.template) -> t.shape) ci.inline = Some Cpp_ir.Foreign.Identity ->
      single_arg
    | _ -> result
  in
  result

(** The constructor [r] of the inductive at [ty] applied to [ts] (the term
    [construction]), not custom, enum or a shared constant: its factory
    call, aggregate or reuse of the token the match freed, each argument
    generated against the field it fills. *)
let gen_construction cx ~expected_ty ~slot env ~ty ~r ~ts (construction : Core.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let slot = into_erased_return cx slot in
  let ty = refined_by_slot slot ty in
  (* Setting [in_constructor_expr] makes unresolvable promoted vars (those
     NOT in [promoted_var_map]) fall back to [Any] = [std::any].

     For non-record constructors (fds = []), we keep [promoted_var_map] so
     that template type annotations (e.g., SigT<..., Path<typename
     _tcI0::Obj>>) match the function's declared return type.

     For record constructors (fds != []), we clear [promoted_var_map]
     because record structs use erased types (std::any) for promoted fields,
     so lambda parameters assigned to record fields must also use std::any. *)
  with_in_constructor_expr cx true @@ fun () ->
  (* A record's arm narrows the map below; the scope puts it back. *)
  with_promoted_var_map cx cx.ctx.lexical.promoted_var_map @@ fun () ->
  (* When an erased argument (a value-dependent leaf boxed as [std::any],
     holding a custom list whose elements are fully erased —
     [deque<std::any>] — at runtime) flows into a constructor/record field
     whose concrete type is a custom list with a NON-erased element type
     (e.g. [mkRec : list elt -> rec] → field [deque<elt>]), the [Core.Expr.Bound_variable]/
     [Core.Expr.Coerce] arg path only unwraps it to the erased [deque<std::any>].
     Convert that to the concrete-element container with [crane_container_cast]
     here, where the field's concrete type is known — a plain aggregate
     initialization / [any_cast<deque<elt>>] would fail, since the value is a
     [deque<std::any>].  Shared by the value-type-variant factory path
     ([gen_and_wrap]) and the record/aggregate path.  Mirrors [eta_fun]'s
     function-argument container-cast path. *)
  let container_cast_erased_field core_ft core_arg (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
    let is_erased_rel =
      match core_arg with
      | Core.Expr.Bound_variable {index = j; occurrence = occ}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _} ->
        Translation_binders.read_is_boxed cx j occ
      | _ -> false
    in
    if not is_erased_rel then expr
    else begin
      let ct = Translation_types.cpp_of_core cx env core_ft in
      let clean_ct =
        Translation_conversion.clean_self_ns ct
      in
      match Translation_conversion.strip_ns_global_app clean_ct with
      | Entity_application (g, [elem_ty], _)
        when Base.Type_util.is_custom_list_global g
             && not (Translation_types.resolves_to_any_type cx elem_ty) ->
        (* [expr] came out as the erased [deque<std::any>] from the
           Core.Expr.Bound_variable/Core.Expr.Coerce path; rebuild it as the concrete element container. *)
        Container_cast (clean_ct, expr, false)
      | _ -> expr
    end
  in
  let fds = record_fields_of_type ty in
  let cons_result = match fds with
  | [] ->
    let c = regular cx env ~expected_ty ty r ts in
    let ts_updated = c.args in
    let temps_from_slot = temps_from_slot cx env ~expected_ty in
    let erase_past_type_arg = erase_past_type_arg ts_updated in
    (* Generate: Type<temps>::ctor::Constructor_(args) *)
    let gen_ctor_call (args : Cpp_ir.Lowered.Expr.t list) : Cpp_ir.Lowered.Expr.t =
      match ty with
      | Core.Type.Global_app {head = n; type_arguments = tys; _} ->
        (* Filter out index type args - only keep parameters *)
        let tys =
          match n with
          | GlobRef.IndRef (kn, _) ->
            ( match Base.Table.get_ind_num_param_vars_opt kn with
            | Some num_param_vars -> safe_firstn num_param_vars tys
            | None -> tys )
          | _ -> tys
        in
        (* Resolve Core.Type.Unknown type args from constructor element types. For
           cons(elem, rest), elem's type provides the list's type param. *)
        let has_unknown =
          List.exists
            (fun (t : Core.Type.t) ->
              match t with
              | Core.Type.Unknown -> true
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
              (fun (t : Core.Type.t) ->
                match t with
                | Core.Type.Unknown ->
                  (* Infer from first non-coercion/Core.Expr.Erased_value constructor arg *)
                  let first_elem =
                    List.find_opt
                      (fun a ->
                        match a with
                        | Core.Expr.Erased_value _ -> false
                        | _ -> true )
                      ts_updated
                  in
                  ( match first_elem with
                  | Some
                      ( Core.Expr.Coerce {value = Core.Expr.Construct {result_type = elem_ty; _}; _}
                      | Core.Expr.Boxed_value {value = Core.Expr.Construct {result_type = elem_ty; _}; _}
                      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Construct {result_type = elem_ty; _}; _} ) ->
                    elem_ty
                  | Some (Core.Expr.Construct {result_type = elem_ty; _}) -> elem_ty
                  | _ -> t )
                | _ -> t )
              tys
          else
            tys
        in
        let temps = Translation_types.template_params_of_core cx ~site:Cpp_ir.Types.Declared env tys in
        (* Where the position expects this very inductive, it -- not the
           constructor's own type annotation -- says how the arguments are
           spelled.  An element type that reached the slot through one of
           the callee's type variables keeps the currying the declaration
           wrote it at, which converting the annotation cannot know: the
           arrows of a function substituted into a type variable are
           indistinguishable from the callee's own. *)
        let temps = temps_from_slot n temps in
        (* Normalize out-of-range [Core.Type.Variable(_, None)] type args to [std::any] when
           this constructor is nested as an argument of another constructor.
           Such a Core.Type.Variable prints as a bogus, undeclared template parameter name
           (e.g. [List<T1>]) — it arises when a value with an erased/promoted
           type parameter (e.g. a record's [Type]-valued field used in a
           dependent [list <that field>] field) is built at a concrete
           instance.  The erased struct field is [std::any], so the value must
           be too.  Restricted to the nested-argument case so a top-level
           constructor call with a genuine (return-only) template parameter
           (e.g. [Trie<T1>::empty()] in a template method) is left intact. *)
        let temps =
          if slot.Translation_slot.in_ctor_arg then List.map Translation_types.erase_unresolved_tvars temps
          else temps
        in
        (* For inductives with dependent parameters (e.g. sigT where the
           second param's type references the first), the dependent type arg
           extracts as a bare reference to the same inductive as an earlier
           arg.  Erase the duplicate to [Any] to avoid mismatched template
           instantiations. *)
        let temps =
          if Base.Table.has_dependent_params n then
            let expected_temps =
              Translation_ctor_args.expected_type_args_from_return cx env ?slot:expected_ty n
                ~arity:(List.length temps)
            in
            match expected_temps with
            | Some exp_tys ->
              List.mapi (fun i t ->
                let exp_t = Translation_types.normalize_erased_types cx (List.nth exp_tys i) in
                if t <> exp_t && Cpp_ir.Types.prints_as_any exp_t then Cpp_ir.Type.Any
                else if t <> exp_t then exp_t
                else t
              ) temps
            | None ->
              match tys with
              | [fst_ty; snd_ty] ->
                let same_base = match fst_ty, snd_ty with
                  | Core.Type.Global_app {head = g1; _}, Core.Type.Global_app {head = g2; type_arguments = sub2; _} ->
                    GlobRef.CanOrd.equal g1 g2 && sub2 = []
                  | _ -> false
                in
                if same_base then
                  match temps with
                  | [fst; _] -> [fst; Cpp_ir.Type.Any]
                  | _ -> temps
                else temps
              | _ -> temps
          else temps
        in
        (* When all template params resolved to [Any] (all type args were
           unresolved Core.Type.Meta), try to recover the concrete element type from
           an expected type threaded down from an enclosing constructor.
           Example: the pair (Fr [...], []) has a concrete pair annotation
           with second type arg list(parser_frame); when generating the nil
           for the second slot, [expected_core_ty] = list(parser_frame),
           so we produce List<Parser_frame>::nil() instead of List<any>::nil(). *)
        let temps =
          (* Treat unnamed Tvars (Core.Type.Variable(_, None)) as erased: they become
             std::any after tvar_erase_type, so we should try to recover
             the concrete type from the expected type annotation. *)
          let is_effectively_erased (t : Cpp_ir.Lowered.Type.t) =
            Cpp_ir.Types.prints_as_any t || (match t with Variable (Index (_, None)) -> true | _ -> false)
          in
          if List.for_all is_effectively_erased temps && temps <> [] then
            (* Resolve any metas in the expected type before matching.
               The let-binding type may be Core.Type.Meta{Some Core.Type.Global_app(...)} so we
               need to unwrap the meta to get the concrete Core.Type.Global_app. *)
            let expected_resolved = Option.map resolve_meta slot.Translation_slot.expected_core_ty
            in
            (match expected_resolved with
            | Some (Core.Type.Global_app {head = exp_n; type_arguments = exp_tys; _})
              when GlobRef.CanOrd.equal n exp_n
                   && List.length exp_tys = List.length tys ->
              (* Compute the recovered type with in_constructor_expr = false so
                 that promoted type vars resolve via promoted_var_map (giving
                 e.g. typename D::Defs::Parser_frame) rather than being erased
                 to std::any by the constructor-expression shortcut. *)
              let recovered =
                with_in_constructor_expr cx false (fun () ->
                    Translation_types.template_params_of_core cx ~site:Cpp_ir.Types.Declared env exp_tys )
              in
              if List.for_all (fun t -> not (Cpp_ir.Types.prints_as_any t)) recovered
              then recovered
              else temps
            | _ -> temps)
          else temps
        in
        let temps = erase_past_type_arg temps in
        (* When this constructor value flows into an erased ([std::any]) slot
           (its slot is [Boxed]) — e.g. a [Prod] pair built inside a
           value-dependent action whose result is boxed into [std::any] —
           erase its type arguments so a "cons" production's element type
           (e.g. [Prod<Nat,Nat>]) matches the canonical erased form the
           matching "nil" production produces (e.g. [Prod<any,any>]).
           Concrete field values implicitly convert to [std::any], so the
           factory call still type-checks.  This mirrors the custom-list
           element erasure in the custom-cons path, extending it to plain
           value-type constructors.  A list is the exception to keeping
           the structure: it goes into a box with its elements boxed one at
           a time ({!Cpp_erasure.erased_list_shape}), so a list of lists is
           a [List<std::any>] whose elements are boxed lists in turn. *)
        let temps =
          if Translation_slot.boxed slot && temps <> [] then
            if is_list_global n then List.map (fun _ -> Cpp_ir.Type.Any) temps
            else List.map index_erase_type temps
          else temps
        in
        (* The slot has already written this constructor's type down -- a
           record field declared at [SigT<std::any, std::any>], say.  At the
           positions it erased, that spelling and not the one recomputed
           from this producer's own instantiation is what the value has to
           be built at, or two producers for one field disagree about the
           erasure and neither initialises it. *)
        (* In a [Boxed] slot, a slot that erases nothing is this value's own
           type, not a statement about which positions are boxed. *)
        let temps =
          let slot_erases_something =
            match expected_ty with
            | Some e -> Base.Type_util.has_tany_in_type (Translation_types.unfold_cpp_typedef cx env e)
            | None -> true
          in
          if Translation_slot.boxed slot && not slot_erases_something then temps
          else temps_from_slot n temps
        in
        (* The factory has to be qualified by the very instantiation the
           declaration spells. *)
        let temps = Translation_tvars.apply_hkt_tyctors cx n temps in
        let temps = Translation_types.ind_promoted_type_args cx n @ temps in
        let ctor_struct = ctor_struct_name_of_ref r in
        let fname = Translation_naming.factory_name_of_ctor r in
        (* Build: Type<temps>::factory(args).  The qualifier is a type, and
           is spelled as one: loopify reads it back off the call to build
           [make_shared], [std::get] and [typename T::Ctor] nodes, and can
           only do that if it is not hidden inside an expression. *)
        let type_expr = Cpp_ir.Type.Entity_application (n, temps, []) in
        (* A factory returns the inductive value at the very instantiation
           the qualifier spells (see [mk_factory_methods] in {!Gen_decls}),
           so the call knows its own result -- and loopify can type a frame
           field holding one instead of falling back on [decltype], and
           spell a cell's constructor struct.  The qualifier is a value's
           spelling; the result is recorded as a type, which only here,
           where the inductives in scope are known, can be written. *)
        let ctor_sig ?constructs args : Cpp_ir.Lowered.phase Cpp_ir.Expr.Call.signature =
          { (Cpp_ir.Build.signature ~yields:(inductive_type cx n temps []) ~nargs:(List.length args) ()) with
            constructs }
        in
        (* Perceus reuse: where the plan gives this construction the token
           of the use_count()==1-guarded arm it is returned from
           ({!Ownership_ir.Region.allocation}), call the [<factory>__reuse] variant
           with the token appended (stored last = printed first, matching
           the [_tok] leading parameter). *)
        ( match cx.ctx.lexical.reuse_token with
        | Some tok when Ownership_ir.Region.allocation cx.ctx.lexical.move_plan construction = Reuse ->
          let args = args @ [Cpp_ir.Expr.Move tok] in
          Call
            ( ctor_sig args,
              Type_member
                (type_expr, Base.Generated_name.companion (Id.of_string fname) "reuse"),
              List.rev args )
        | _ ->
          if
            Translation_suspension.suspends_constructor cx ~self:cx.ctx.input.body_owner
              ~binder_type:(get_env_type_opt cx) n
              ts
          then
            (* The arguments are read where the thunk is made, and taken
               by move there when the plan moves them. *)
            let moved = moved_names env (Ownership_ir.Region.eta_captures cx.ctx.lexical.move_plan ts) in
            Translation_suspension.suspend_ctor ~moved type_expr (Id.of_string ctor_struct) (List.rev args)
          else
            Call
              ( ctor_sig ~constructs:r args,
                Type_member (type_expr, Id.of_string fname),
                List.rev args ) )
      | _ ->
        (* Fallback for non-Core.Type.Global_app types *)
        let fname = Translation_naming.factory_name_of_ctor r in
        Call
          ( {(Cpp_ir.Build.signature ~nargs:(List.length args) ()) with constructs = Some r},
            Type_member (Entity_application (r, [], []), Id.of_string fname),
            List.rev args )
    in
    (* [gen_ctor_call] is handed its arguments last first, as the
       [List.rev (List.mapi ...)] at its call builds them, and reverses them
       into the source order a [Call] holds. *)
    let gen_ctor_arg ?expected_ty ?(slot = slot) e =
      gen_stored_value cx ?expected_ty ~slot env e
    in
    (* When a constructor's field type is a type variable (Core.Type.Variable i) that
       resolves to an owning pointer type (because T is in method_self_ns),
       the generated arg expression is a bare T value.  Wrap it so the
       field's stored type matches. *)
    let ty_core_tparams = c.ty_core_tparams in
    (* The result type of a function-valued constructor field whose declared
       type is [Core.Type.Variable i].  The [Core.Expr.Construct]'s own type arguments say what [i]
       stands for -- [nat -> nat], say -- so peeling off the [n_params]
       arrows the generated lambda consumes leaves the codomain.

       This is the only source for the answer: reading it back off the
       lambda that was already generated would take one branch's [return]
       for the whole function's result type.  [None] where the type
       arguments do not reach that far, as for a type-INDEXED inductive,
       which has none; each caller then supplies its own default. *)
    let field_fun_ret_ty i n_params =
      match if i >= 1 then List.nth_opt ty_core_tparams (i - 1) else None with
      | None -> None
      | Some actual_core_ty -> (
        match strip_arrows_n n_params (resolve_meta actual_core_ty) with
        | Some ret_core -> Some (strip_cpp_ref_const (Translation_types.cpp_of_core cx env ret_core))
        | None -> None )
    in
    let ctor_temps = c.ctor_temps and field_types = c.field_types in
    let wrap_if_needed_for_field ft core_e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
      match ft with
      | Core.Type.Variable {variable = i; _} ->
        ( try
          let ct = List.nth ctor_temps (i - 1) in
          match ct with
          | Shared_pointer inner ->
            let inner_g = match inner with
              | Entity_application (g, _, _) -> Some g | _ -> None in
            ( match inner_g with
            | Some g when Core.Ref.User.Set.mem g cx.ctx.input.method_self_ns ->
              Cpp_ir.Build.call (Allocate (Heap, inner)) [expr]
            | _ -> expr )
          | ct when Cpp_ir.Types.prints_as_any ct
                    || (match ct with
                        | Entity_application (g, [], _) -> Base.Table.is_erased_type_const g
                        | _ -> false) ->
            ( match expr with
            | Lambda
              ({ params = params;
                 return_type = ret_ty_opt;
                 body = body_stmts;
                 capture = cap; _ } as lam) ->
              let params = List.rev params in
              let n_params = List.length params in
              let new_params = List.map (fun (orig_ty, orig_id) ->
                let bare = strip_cpp_ref_const orig_ty in
                if bare <> Cpp_ir.Type.Any then (Cpp_ir.Type.Const (Reference (Lvalue, Cpp_ir.Type.Any)), orig_id)
                else (orig_ty, orig_id)
              ) params in
              let core_concrete_param_tys =
                let rec collect_lam_tys = function
                  | Core.Expr.Lambda {parameter_type = ty; body; _} -> ty :: collect_lam_tys body
                  | Core.Expr.Coerce {value = inner; _}
                  | Core.Expr.Boxed_value {value = inner; _}
                  | Core.Expr.Lambda_group_barrier {value = inner; _} ->
                    collect_lam_tys inner
                  | _ -> []
                in
                collect_lam_tys core_e
              in
              let expand_core_type core_ty =
                let abbrev r = match r with
                  | GlobRef.ConstRef kn -> Base.Table.lookup_typedef_unchecked kn
                  | _ -> None
                in
                Base.Core_util.type_expand abbrev core_ty
              in
              (* Canonical erased shape for a list-typed erased param is
                 [deque<std::any>] -- a bare [std::any] per element, not a
                 structure-preserving [deque<pair<any,any>>].  A sibling
                 producer for the same Coq list type (e.g. the base-case
                 action of the same [SigT] action family) may erase to the
                 flat shape; casting this parameter to the
                 structure-preserving shape would then throw
                 [std::bad_any_cast] at runtime.  See the matching
                 invariant in [gen_expr]'s [Core.Expr.Bound_variable]/[Core.Expr.Coerce] cases. *)
              let erase_custom_list_elems : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                | Entity_application (g, _ :: _, ns) when Base.Type_util.is_custom_list_global g ->
                  Entity_application (g, [Cpp_ir.Type.Any], ns)
                | t -> t
              in
              let core_body_ret_ty =
                let rec get_body = function
                  | Core.Expr.Lambda {body; _} -> get_body body
                  | Core.Expr.Coerce {value = inner; _}
                  | Core.Expr.Boxed_value {value = inner; _}
                  | Core.Expr.Lambda_group_barrier {value = inner; _} ->
                    get_body inner
                  | body -> infer_core_body_type body
                in
                get_body core_e
              in
              let erase_inner_tparams : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                | Entity_application (g, (_ :: _), ns) when is_list_global g ->
                  (* Canonical erased shape for a list is [deque<any>],
                     a bare [std::any] per element, not a
                     structure-preserving [deque<pair<any,any>>]. *)
                  Entity_application (g, [Cpp_ir.Type.Any], ns)
                | Entity_application (g, args, m) ->
                  let erase_t : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                    | Entity_application (g2, args2, ns2) ->
                      Entity_application (g2, List.map (fun _ -> Cpp_ir.Type.Any) args2, ns2)
                    | _ -> Cpp_ir.Type.Any
                  in
                  Entity_application (g, List.map erase_t args, m)
                | t -> t
              in
              let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
                match orig_id with
                | None -> None
                | Some id ->
                  let bare = strip_cpp_ref_const (fst (List.nth params j)) in
                  if bare = Cpp_ir.Type.Any then None
                  else
                    let concrete_ty =
                      let from_annotation =
                        match List.nth_opt core_concrete_param_tys j with
                        | Some core_ty ->
                          let expanded = expand_core_type core_ty in
                          let ct = Translation_types.cpp_of_core cx env expanded in
                          erase_custom_list_elems (strip_cpp_ref_const ct)
                        | None -> bare
                      in
                      if not (Translation_types.resolves_to_any_type cx from_annotation) then from_annotation
                      else begin
                        let ret_ct = match core_body_ret_ty with
                          | Some ret_core ->
                            let ct = Translation_types.cpp_of_core cx env ret_core in
                            strip_cpp_ref_const ct
                          | None -> Cpp_ir.Type.Any
                        in
                        erase_inner_tparams ret_ct
                      end
                    in
                    if Translation_types.resolves_to_any_type cx concrete_ty then None
                    else
                      let any_id = Id.of_string ("_any_" ^ Id.to_string id) in
                      Some (id, any_id, concrete_ty)
              ) (List.mapi (fun idx p -> (idx, p)) new_params) in
              let new_body =
                List.fold_left (fun stmts (orig_id, any_id, concrete_ty) ->
                  let cast_stmt = Cpp_ir.Stmt.Bind_variable (orig_id, Declare (concrete_ty, None),
                    Cpp_erasure.unbox concrete_ty (Cpp_ir.Expr.Local any_id)) in
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
                | None -> Cpp_ir.Type.Any
              in
              let new_ret_ty = match ret_ty_opt with
                | Some _ -> ret_ty_opt
                | None -> if erased_ret_ty <> Cpp_ir.Type.Any then Some erased_ret_ty else None
              in
              let new_lambda = erased_lambda lam
                  ~params:(List.rev renamed_params)
                  ~ret:new_ret_ty
                  ~body:new_body in
              (* The field itself is fully erased, so the only signature a
                 consumer can cast back to is the canonical
                 [std::function<std::any(std::any...)>] -- the same one the
                 non-lambda case below stores.  The lambda keeps its own
                 concrete result type; [crane_erase_fn] deduces it and boxes
                 what it returns. *)
              Erase_callable (Boxed_whole, new_lambda)
            | _ ->
              (* When a custom list literal (e.g. deque<Val>) is stored in a
                 std::any field, regenerate it in a [Boxed] slot so
                 elements are erased to std::any.  The stored value becomes
                 deque<any>, matching what any_cast<deque<any>> expects when
                 consuming through the erased field. *)
              let rec is_custom_list_cons = function
                | Core.Expr.Construct {constructor = GlobRef.ConstructRef ((kn, _), _); _} ->
                  let ind = GlobRef.IndRef (kn, 0) in
                  Base.Type_util.is_custom_list_global ind
                | Core.Expr.Coerce {value = inner; _}
                | Core.Expr.Boxed_value {value = inner; _}
                | Core.Expr.Lambda_group_barrier {value = inner; _} ->
                  is_custom_list_cons inner
                | _ -> false
              in
              if is_custom_list_cons core_e then begin
                gen_ctor_arg ~slot:(Translation_slot.into_box Var_box slot) core_e
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
                   value-dependent (erased to [std::any] in the generic Core
                   type), so the concrete argument types needed for the
                   [any_cast] inside the adapter are only known at C++
                   instantiation.  Rather than reconstruct them here, defer to
                   the [crane_erase_fn] runtime helper, which uses
                   [std::function] CTAD to deduce the callable's signature and
                   builds the [std::function<std::any(std::any...)>] adapter
                   (unbox each argument, box the result). *)
                (* Wrap via the [crane_erase_fn] runtime helper (emitted as
                   [#include "crane_fn.h"] in the header preamble). *)
                Translation_coerce.box_for_any_slot cx Var_box core_e expr
              end )
          | Function (param_tys, ret_ty) when List.exists (fun t -> t = Cpp_ir.Type.Any) param_tys ->
            ( match expr with
            | Lambda
              ({ params = params;
                 return_type = ret_ty_opt;
                 body = body_stmts;
                 capture = cap; _ } as lam) ->
              let params = List.rev params in
              let n_params = List.length params in
              let new_params = List.mapi (fun j (orig_ty, orig_id) ->
                if j < List.length param_tys && List.nth param_tys j = Cpp_ir.Type.Any then
                  let bare = strip_cpp_ref_const orig_ty in
                  if bare <> Cpp_ir.Type.Any then (Cpp_ir.Type.Const (Reference (Lvalue, Cpp_ir.Type.Any)), orig_id)
                  else (orig_ty, orig_id)
                else (orig_ty, orig_id)
              ) params in
              let core_body_ret_ty =
                let rec get_body = function
                  | Core.Expr.Lambda {body; _} -> get_body body
                  | Core.Expr.Coerce {value = inner; _}
                  | Core.Expr.Boxed_value {value = inner; _}
                  | Core.Expr.Lambda_group_barrier {value = inner; _} ->
                    get_body inner
                  | body -> infer_core_body_type body
                in
                get_body core_e
              in
              let core_concrete_param_tys =
                let rec collect_lam_tys = function
                  | Core.Expr.Lambda {parameter_type = ty; body; _} -> ty :: collect_lam_tys body
                  | Core.Expr.Coerce {value = inner; _}
                  | Core.Expr.Boxed_value {value = inner; _}
                  | Core.Expr.Lambda_group_barrier {value = inner; _} ->
                    collect_lam_tys inner
                  | _ -> []
                in
                collect_lam_tys core_e
              in
              let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
                if j < List.length param_tys && List.nth param_tys j = Cpp_ir.Type.Any then
                  match orig_id with
                  | None -> None
                  | Some id ->
                    let concrete_ty =
                      let from_annotation =
                        match List.nth_opt core_concrete_param_tys j with
                        | Some core_ty ->
                          let ct = Translation_types.cpp_of_core cx env core_ty in
                          strip_cpp_ref_const ct
                        | None -> Cpp_ir.Type.Any
                      in
                      if not (Translation_types.resolves_to_any_type cx from_annotation) then
                        from_annotation
                      else begin
                        let ret_ct = match core_body_ret_ty with
                        | Some ret_core ->
                          let ct = Translation_types.cpp_of_core cx env ret_core in
                          strip_cpp_ref_const ct
                        | None -> Cpp_ir.Type.Any
                        in
                        let erase_inner_tparams : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                          | Entity_application (g, args, m) ->
                            let erase_t : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                              | Entity_application (g2, args2, ns2) ->
                                Entity_application (g2, List.map (fun _ -> Cpp_ir.Type.Any) args2, ns2)
                              | _ -> Cpp_ir.Type.Any
                            in
                            Entity_application (g, List.map erase_t args, m)
                          | t -> t
                        in
                        erase_inner_tparams ret_ct
                      end
                    in
                    (* Canonical erased shape for a list-typed erased param
                       is [deque<std::any>] -- a bare [std::any] per
                       element, not a structure-preserving
                       [deque<pair<any,any>>].  See the matching invariant
                       in [gen_expr]'s [Core.Expr.Bound_variable]/[Core.Expr.Coerce] cases. *)
                    let concrete_ty : Cpp_ir.Lowered.Type.t =
                      match concrete_ty with
                      | Entity_application (g, _ :: _, ns) when is_list_global g ->
                        Entity_application (g, [Cpp_ir.Type.Any], ns)
                      | In_namespace (ns_g, Entity_application (g, _ :: _, ns))
                        when is_list_global g ->
                        In_namespace (ns_g, Entity_application (g, [Cpp_ir.Type.Any], ns))
                      | t -> t
                    in
                    if Translation_types.resolves_to_any_type cx concrete_ty then None
                    else
                      let any_id = Id.of_string ("_any_" ^ Id.to_string id) in
                      Some (id, any_id, concrete_ty)
                else None
              ) (List.mapi (fun idx p -> (idx, p)) new_params) in
              let new_body =
                List.fold_left (fun stmts (orig_id, any_id, concrete_ty) ->
                  let cast_stmt = Cpp_ir.Stmt.Bind_variable (orig_id, Declare (concrete_ty, None),
                    Cpp_erasure.unbox concrete_ty (Cpp_ir.Expr.Local any_id)) in
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
              let erased_param_tys = List.map (fun _ -> Cpp_ir.Type.Any) renamed_params in
              let erased_ret_ty =
                match field_fun_ret_ty i n_params with
                | Some t -> t
                | None -> Cpp_ir.Type.Any
              in
              let new_ret_ty = match ret_ty_opt with
                | Some _ -> ret_ty_opt
                | None -> if erased_ret_ty <> Cpp_ir.Type.Any then Some erased_ret_ty else None
              in
              let new_lambda = erased_lambda lam
                  ~params:(List.rev renamed_params)
                  ~ret:new_ret_ty
                  ~body:new_body in
              let func_ty = Cpp_ir.Type.Function (safe_firstn n_params erased_param_tys, erased_ret_ty) in
              Cpp_erasure.converting_ctor func_ty [new_lambda]
            (* A function value that is not a lambda literal (a reference to a
               global, or a methodified one) cannot have its parameters
               rewritten the way the branch above rewrites a literal's, so
               defer the adaptation to the runtime helper, which deduces the
               callable's signature and unboxes each argument.  The field's
               own codomain stays concrete. *)
            | _ when Translation_erasure.core_expr_is_function_value cx core_e ->
              Erase_callable (At_signature ret_ty, expr)
            | _ -> expr )
          | _ -> expr
          with Failure _ | Invalid_argument _ ->
            (* Field type index is beyond ctor_temps — this field is erased
               to std::any.  If the expression is a lambda, wrap it in
               std::function so that std::any stores the type-erased wrapper
               and any_cast<std::function<...>> can recover it. *)
            match expr with
            | Lambda
              { params = params;
                return_type = ret_ty_opt;
                body = body_stmts;
                _ } ->
              let params = List.rev params in
              let param_types = List.map (fun (ty, _) ->
                strip_cpp_ref_const ty) params in
              let ret_ty = match ret_ty_opt with
                | Some ty -> strip_cpp_ref_const ty
                | None ->
                  ( match
                      field_fun_ret_ty i (List.length param_types)
                    with
                  | Some t -> t
                  | None -> Cpp_ir.Type.Void )
              in
              Cpp_erasure.converting_ctor (Cpp_ir.Type.Function (param_types, ret_ty)) [expr]
            | _ -> expr )
      | ft ->
        (* Handle arrow types containing erased type variables.
           E.g. field type Core.Type.Arrow(Core.Type.Variable 1,
           Core.Type.Global_app(nat)) where Core.Type.Variable 1 is erased: the
           concrete lambda [](uint64_t x){return x*x;} must become [](std::any
           _a0){return any_cast<uint64_t>(_a0) * any_cast<uint64_t>(_a0);} so it
           matches the factory param std::function<uint64_t(std::any)>. *)
        let tvar_is_erased i =
          try match List.nth ctor_temps (i - 1) with
            | Any -> true | _ -> false
          with Failure _ | Invalid_argument _ -> true
        in
        let rec ft_has_erased_tvar = function
          | Core.Type.Variable {variable = i; _} -> tvar_is_erased i
          | Core.Type.Unknown -> true
          (* A type computed from a value -- [memCType c] -- erases to
             [std::any] as surely as an erased variable does. *)
          | Core.Type.Global_app {head = g; _}
            when Base.Table.is_value_dep_type_scheme g || Base.Table.is_erased_type_const g ->
            true
          | Core.Type.Arrow {parameter = a; result = b} -> ft_has_erased_tvar a || ft_has_erased_tvar b
          | _ -> false
        in
        ( match ft, expr with
        | Core.Type.Arrow _, Lambda
          ({ params = params;
             return_type = ret_ty_opt;
             body = body_stmts;
             capture = cap; _ } as lam)
          when ft_has_erased_tvar ft ->
          let params = List.rev params in
          let rec collect_arrows = function
            | Core.Type.Arrow {parameter = a; result = rest} ->
              let (ps, r) = collect_arrows rest in (a :: ps, r)
            | t -> ([], t)
          in
          let (core_param_tys, core_ret_ty) = collect_arrows ft in
          (* The field's type is written in the inductive's variables, not
             this scope's: [k : X -> T] names the constructor's third
             parameter, which this call instantiates through [ctor_temps]. *)
          let erase_core_ty t =
            match t with
            | Core.Type.Variable {variable = i; _} when tvar_is_erased i -> Cpp_ir.Type.Any
            | Core.Type.Unknown -> Cpp_ir.Type.Any
            | _ ->
                Cpp_ir.Types.substitute
                   (fun i -> if i >= 1 then List.nth_opt ctor_temps (i - 1) else None)
                   (Translation_types.cpp_of_core cx env t)
          in
          let erased_param_tys = List.map erase_core_ty core_param_tys in
          let erased_ret_ty = erase_core_ty core_ret_ty in
          let n_params = List.length params in
          (* Build new params with std::any for erased positions, and add
             any_cast let-bindings for each erased parameter at the start
             of the body. *)
          let new_params = List.mapi (fun j (orig_ty, orig_id) ->
            let erased_ty =
              if j < List.length erased_param_tys
                 && List.nth erased_param_tys j = Cpp_ir.Type.Any
                 && strip_cpp_ref_const orig_ty <> Cpp_ir.Type.Any
              then
                (* Replace concrete type with std::any, preserving const ref *)
                Cpp_ir.Type.Const (Reference (Lvalue, Cpp_ir.Type.Any))
              else orig_ty
            in
            (erased_ty, orig_id)
          ) params in
          (* Extract concrete parameter types from the Core lambda *)
          let core_concrete_param_tys =
            let rec collect_lam_tys = function
              | Core.Expr.Lambda {parameter_type = ty; body; _} -> ty :: collect_lam_tys body
              | Core.Expr.Coerce {value = inner; _}
              | Core.Expr.Boxed_value {value = inner; _}
              | Core.Expr.Lambda_group_barrier {value = inner; _} ->
                collect_lam_tys inner
              | _ -> []
            in
            collect_lam_tys core_e
          in
          let cast_bindings = List.filter_map (fun (j, (_orig_ty, orig_id)) ->
            if j < List.length erased_param_tys
               && List.nth erased_param_tys j = Cpp_ir.Type.Any then
              match orig_id with
              | Some id ->
                (* Get concrete type from the Core lambda param, not the C++ lambda *)
                let concrete_ty =
                  match List.nth_opt core_concrete_param_tys j with
                  | Some core_ty ->
                    let ct = Translation_types.cpp_of_core cx env core_ty in
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
                   invariant in [gen_expr]'s [Core.Expr.Bound_variable]/[Core.Expr.Coerce] cases. *)
                let concrete_ty : Cpp_ir.Lowered.Type.t =
                  match concrete_ty with
                  | Entity_application (g, _ :: _, ns) when is_list_global g ->
                    Entity_application (g, [Cpp_ir.Type.Any], ns)
                  | In_namespace (ns_g, Entity_application (g, _ :: _, ns))
                    when is_list_global g ->
                    In_namespace (ns_g, Entity_application (g, [Cpp_ir.Type.Any], ns))
                  | t -> t
                in
                (* [Obligation Opaque_type] is no more castable than [Any]: both print
                   as [std::any], and neither names a representation to
                   recover the parameter into. *)
                if (not (Cpp_ir.Types.prints_as_any concrete_ty)) && concrete_ty <> Cpp_ir.Type.Auto
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
            Cpp_ir.Stmt.Bind_variable (orig_id, Declare (concrete_ty, None),
              Cpp_erasure.unbox concrete_ty (Cpp_ir.Expr.Local any_id))
          ) cast_bindings in
          let new_body = cast_stmts @ body_stmts in
          let new_ret_ty = match ret_ty_opt with
            | Some _ -> ret_ty_opt
            | None -> if erased_ret_ty <> Cpp_ir.Type.Any then Some erased_ret_ty else None
          in
          let new_lambda = erased_lambda lam
              ~params:(List.rev new_params)
              ~ret:new_ret_ty
              ~body:new_body in
          let func_ty = Cpp_ir.Type.Function (safe_firstn n_params erased_param_tys, erased_ret_ty) in
          Cpp_erasure.converting_ctor func_ty [new_lambda]
        (* The same erased-argument adaptation, for a function value that is
           not a lambda literal (a reference to a global, or to a method):
           there are no parameters here to rewrite, so defer to the runtime
           helper, which deduces the callable's signature and unboxes each
           argument.  The field's codomain stays concrete. *)
        | Core.Type.Arrow _, _ when ft_has_erased_tvar ft && Translation_erasure.core_expr_is_function_value cx
          core_e ->
          let rec codomain = function
            | Core.Type.Arrow {result = rest; _} -> codomain rest
            | t -> t
          in
          let ret_ty = Translation_types.cpp_of_core cx env (codomain ft) in
          let expr = Translation_coerce.erased_fn_instantiation expr in
          Erase_callable (At_signature (if Cpp_ir.Types.prints_as_any ret_ty then Cpp_ir.Type.Any else ret_ty), expr)
        (* A field erased whole -- [den t], whatever [t] the call names --
           holds a function as the canonical callable it is read back as. *)
        | _ when ft_has_erased_tvar ft ->
          Translation_coerce.box_for_any_slot cx
            (Translation_types.box_kind_of_cpp_type (Translation_types.cpp_of_core cx env ft))
            core_e expr
        | _ -> expr )
    in
    let gen_and_wrap i e =
      let ft_opt, expr =
        (* A constructor argument returns its own value, not the enclosing
           function's, so the ambient return type must not reach it. *)
        with_cpp_return_type cx None (fun () ->
        let ft_opt =
          try Some (List.nth field_types i)
          with Failure _ | Invalid_argument _ -> None
        in
        let expected_for_arg, arg_slot = regular_field cx env ~is_boxed:(Translation_binders.read_is_boxed cx)
          c ~slot i e in
        let expr = gen_ctor_arg ~slot:arg_slot ?expected_ty:expected_for_arg e in
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
      (* A variable going into a field that holds the inductive itself is
         marked, so that where the variable turns out to be a field read
         out of a matched value ([*p]), the new node shares [p]'s cell
         rather than copying the child into a new one (see
         [Cpp_ir.Crane_rt.Share_child] and the factory's [crane::child_slot]). *)
      let shares_child =
        Translation_state.non_atomic_rc cx
        && (match expr with Local _ -> true | _ -> false)
        && match ft_opt, resolve_meta ty with
           | Some ft, Core.Type.Global_app {head = n_ind; _} ->
             (match resolve_meta ft with
              | Core.Type.Global_app {head = g; _} -> globref_equal g n_ind
              | _ -> false)
             && (not (Base.Table.is_coinductive n_ind))
             && not (Base.Table.is_shared_variant n_ind)
           | _ -> false
      in
      if shares_child then Cpp_ir.Build.call (Runtime Cpp_ir.Crane_rt.Share_child) [expr] else expr
    in
    gen_ctor_call (List.rev (List.mapi gen_and_wrap ts_updated))
  | _ ->
    (* Records: a record struct erases the promoted variables it does not
       take as parameters to [std::any], so a lambda assigned to one of its
       fields has to spell them that way too, and the scope forgets how to
       resolve them.  The ones it mentions without declaring are parameters
       of the struct like any other inductive's (see
       {!Translation_types.ind_promoted_type_args}), so its fields spell them resolved, and so
       must everything built for them here. *)
    set_lexical cx (fun l -> { l with promoted_var_map = record_promoted_map cx ty });
    let nstempmod args : Cpp_ir.Lowered.Expr.t =
      match ty with
      | Core.Type.Global_app {head = n; type_arguments = tys; _} ->
        (* Filter out index type args - only keep parameters *)
        let tys =
          match n with
          | GlobRef.IndRef (kn, _) ->
            ( match Base.Table.get_ind_num_param_vars_opt kn with
            | Some num_param_vars -> safe_firstn num_param_vars tys
            | None -> tys )
          | _ -> tys
        in
        (* Named against the enclosing scope's type variables.  Inside an
           instance member template a recovered [Core.Type.Variable 3] is the method's
           own [_A0], and an empty name list spells it as the anonymous
           [T3] -- a free name where the erasure at least compiled. *)
        let temps =
          Translation_types.ind_promoted_type_args cx n
          @ Translation_types.template_params_of_core cx ~site:Cpp_ir.Types.Through_tvar env tys
        in
        if Base.Table.is_coinductive n then
          Cpp_ir.Build.call
            (Allocate (Heap, Entity_application (n, temps, [])))
            [Aggregate {struct_ = n; type_args = temps; values = args}]
        else
          (* Value-type records: direct construction, no make_shared *)
          Aggregate {struct_ = n; type_args = temps; values = args}
      | _ ->
        CErrors.anomaly
          (Pp.str
             "gen_expr: non-record Construct with matching type expected Global_app" )
    in
    let record_arg_exprs =
      let field_types_rec = record_field_types r in
      let tvars = get_current_type_vars cx in
      let declared_field_cpp_ty = record_declared_field_cpp_ty cx env ty in
      let base_args =
        List.mapi
          (fun i e ->
            let expected_ty, slot = record_field cx env ~is_boxed:(Translation_binders.read_is_boxed cx) ty r
              ~slot i e in
            gen_stored_value cx ~slot ?expected_ty env e)
          ts
      in
      match ty with
      | Core.Type.Global_app {head = n; _} ->
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
              let storage_ty = Translation_types.cpp_ir_of_core_type cx env ~ns:(Core.Ref.User.Set.singleton n) tvars ft in
              let api_ty = Translation_types.cpp_of_core cx env ft in
              (* A closure written at the concrete domain does not convert
                 to the erased signature the field is declared at, nor is it
                 the canonical callable a field erased whole ([den t] at a
                 [TFun] index) is read back as; [coerce] supplies the
                 [crane_erase_fn] adapter for the one, and
                 {!Translation_coerce.box_for_any_slot} for the other. *)
              let declared_ty = declared_field_cpp_ty ft in
              let expr =
                if erased_domain_fun_ty declared_ty then
                  Translation_coerce.coerce cx ?term:(List.nth_opt ts i) ~into:declared_ty expr
                else if Cpp_ir.Types.prints_as_any (Translation_types.unfold_cpp_typedef cx env declared_ty) then
                  match List.nth_opt ts i with
                  | Some e ->
                    Translation_coerce.box_for_any_slot cx (Translation_types.box_kind_of_cpp_type declared_ty) e expr
                  | None -> expr
                else expr
              in
              Translation_conversion.wrap_storage_expr ~storage_ty ~api_ty expr
            | None -> expr)
          base_args
      | _ -> base_args
    in
    nstempmod record_arg_exprs
  in
  cons_result
