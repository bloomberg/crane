(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type aliases and top-level functions and constants: the function head
    and body, declarations, and the generated-entity record a function's
    file views come from. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Translation
open Plan_templates
open Gen_context
open Gen_records

module IntSet = Escape.IntSet

(** Build the [using] declaration for a type alias.

    [ot] is [None] for a signature entry that names a type without defining it.
    The three irregular right-hand sides -- a custom extraction's verbatim
    spelling, an axiom's [std::any] placeholder, and an absent definition --
    are all expressed as {!Minicpp.dusing} fields rather than as a rendered
    string handed to the printer. *)
let gen_type_alias r vars ot =
  let vars = rename_tvars Cpp_state.keywords vars in
  let du_rhs, du_note =
    with_method_ns_for_locals @@ fun () ->
    match Cpp_state.find_type_custom_opt r with
    | Some (_ids, s) -> (Some (Tid_external (s, [])), None)
    | None -> (
      match ot with
      | None -> (None, None)
      | Some Taxiom ->
        Cpp_erasure.register_axiom_type r;
        Table.add_erased_type_const r;
        require_obj_header ();
        (Some Tany, Some "AXIOM TO BE REALIZED")
      | Some t ->
        (* Name the body's type variables from the alias's own list.  Left
           anonymous they are resolved by position against the emitted
           parameters, and the promoted ones lead (they are defaulted, and a
           default may not precede a plain parameter) -- so [Definition Top :=
           itree TopE], eta-expanded to supply [itree]'s missing value
           parameter, read the value slot off the FRONT and wrote [ITree<iptr>].
           Eta-expansion appends; positional resolution reads from the
           beginning. *)
        (Some (convert_ml_type_to_cpp_type (empty_env ()) vars t), None) )
  in
  let du_tparams_head =
    hkt_templates ?applied:du_rhs r vars
      (match ot with Some t -> [t] | None -> [])
  in
  let du_tparams =
    List.map (fun v -> (TTtypename, v)) (Table.promoted_type_params r)
    @ du_tparams_head
  in
  (* A family parameter [hkt_templates] left plain is still written applied
     in the rendering; the applied family is the family's own struct. *)
  let du_rhs =
    let plain =
      List.filter_map
        (fun (tt, id) -> match tt with TTtemplate _ -> None | _ -> Some id)
        du_tparams
    in
    let in_scope = List.map snd du_tparams in
    Option.map
      (map_cpp_type (function
        | Tapply (head, args) when List.exists (fun id -> tvar_is id head) plain ->
          Minicpp.rebind_plain_var ~in_scope head args
        | t -> t ))
      du_rhs
  in
  Dusing {du_tparams; du_name = r; du_rhs; du_note}

(** Substitute [CPPglob id] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion.

    Identity here is the {i user} name, not the canonical one {!globref_equal}
    compares.  Every caller substitutes a declaration's own reference for a
    self-call, and what makes an occurrence a self-call is that it is printed at
    the name being declared -- a property of the user name, since that is the
    one the C++ spelling comes from.  Two references can share a canonical name
    and still be different C++ names: [Include M] inside a functor re-exports
    [M]'s fields as constants of the including module, so the forwarder's body
    and the forwarder itself agree canonically and differ in exactly the
    qualifier that keeps the call from being a call to itself. *)
let rec glob_subst_expr (id : GlobRef.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPglob (id', _, _) when GlobRef.UserOrd.equal id id' ->
    repl
  | _ -> map_expr (glob_subst_expr id repl) (glob_subst_stmt id repl) Fun.id e

(** Statement-level case of {!glob_subst_expr}. *)
and glob_subst_stmt (id : GlobRef.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt (glob_subst_expr id repl) (glob_subst_stmt id repl) Fun.id s

(** Substitute [CPPvar id] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion. *)
let rec var_subst_expr (id : Id.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPvar id' when Id.equal id id' -> repl
  | _ -> map_expr (var_subst_expr id repl) (var_subst_stmt id repl) Fun.id e

(** Statement-level case of {!var_subst_expr}. *)
and var_subst_stmt (id : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt (var_subst_expr id repl) (var_subst_stmt id repl) Fun.id s

(** Substitute unnamed type variables with named ones based on a variable list.
    This is used when generating methods to replace T1, T2, etc. with the
    struct's template parameter names like A, B, etc. Uses [map_cpp_type] for
    structural recursion on types. *)
let tvar_subst_type (tvars : Id.t list) : cpp_type -> cpp_type =
  map_cpp_type (fun ty ->
    match ty with
    | Tvar (Tv_index (i, None)) ->
      (try Tvar (Tv_index (i, Some (List.nth tvars (pred i)))) with Failure _ -> ty)
    | _ -> ty )

(** Substitute type variables in expressions and statements. Uses generic AST
    visitors for structural recursion. *)
let rec tvar_subst_expr (tvars : Id.t list) (e : cpp_expr) : cpp_expr =
  map_expr
    (tvar_subst_expr tvars)
    (tvar_subst_stmt tvars)
    (tvar_subst_type tvars)
    e

(** Statement-level case of {!tvar_subst_expr}. *)
and tvar_subst_stmt (tvars : Id.t list) (s : cpp_stmt) : cpp_stmt =
  map_stmt
    (tvar_subst_expr tvars)
    (tvar_subst_stmt tvars)
    (tvar_subst_type tvars)
    s

(** [is_unit_cpp_type ty] is [true] for the C++ rendering of Rocq's [unit]
    (which [Shared.v] maps to [std::monostate]) and for [void]. *)
let is_unit_cpp_type = function
  | Tvoid -> true
  | Tglob (r, _, _) | Tnamespace (r, _) -> Table.is_unit_type r
  | _ -> false

(** [dead_unit_returns_to_abort cod body] rewrites [return tt;] into a throw
    when the enclosing function does not return [unit].

    A dependent match can have branches that are impossible by typing, e.g.

    {v
      match v in vec _ m return match m with O => unit | S _ => nat end with
      | vnil => tt
      | vcons _ x _ => x
      end
    v}

    Extraction erases the dependency, so the [vnil] branch survives as a plain
    [tt] sitting in a function whose C++ return type is [uint64_t] — which does
    not compile.  The branch is unreachable, so emit the same throw used for
    other absurd cases.

    A nested lambda is traversed under its own declared return type, since a
    [tt] returned from a lambda that really does return [unit] is well-typed. *)
let dead_unit_returns_to_abort (cod : cpp_type) (body : cpp_stmt list) =
  (* A [tt] can also reach the return as the head of a call, when the branch's
     type is a function type and eta-expansion pushed the invented argument
     inside the match: the impossible branch then returns [tt(x)].  Applying a
     value that carries no information is no more reachable than returning
     one, and is the same branch seen one step later. *)
  let rec is_tt = function
    | CPPglob (r, _, _) -> Table.is_tt_constructor r
    | CPPfun_call (_, f, _) -> is_tt f
    | _ -> false
  in
  (* [ret_ty] is [None] inside a lambda with a deduced return type: there is no
     declared type to contradict, so leave those bodies alone. *)
  let rec fix_stmts ret_ty stmts =
    match ret_ty with
    | Some t when not (is_unit_cpp_type t) -> List.map (fix_stmt ret_ty) stmts
    | _ -> List.map (fix_stmt None) stmts
  and fix_stmt ret_ty s =
    match s with
    | Sreturn (Some e) when ret_ty <> None && is_tt e ->
      Sreturn
        (Some
           (CPPabort
              ( Minicpp.dead_branch_message,
                (match ret_ty with Some t -> t | None -> Tany) )))
    | _ -> map_stmt (fix_expr ret_ty) (fix_stmt ret_ty) (fun t -> t) s
  and fix_expr ret_ty e =
    match e with
    | CPPlambda l ->
      CPPlambda {l with cl_body = fix_stmts l.cl_ret l.cl_body}
    | _ -> map_expr (fix_expr ret_ty) (fix_stmt ret_ty) (fun t -> t) e
  in
  fix_stmts (Some cod) body

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
    (body : ml_ast) : int list =
  detect_non_forwarded_params_generic
    ~is_self_call:(fun _depth -> function
      | MLglob (r, _) -> globref_equal r self_ref
      | _ -> false )
    n_params body

(** The C++ expression stating the witness held by a [sig]-typed parameter
    called [name], when it can be stated at all.  A transparently extracted
    [sig] {i is} its witness, so the parameter stands for it; one left as a
    struct carries the witness in the field its single constructor registered.
    Either way the predicates that reach here compare the witness numerically,
    so a witness that is not a C++ scalar has nothing to compare and the
    precondition can only be reported as a comment. *)
let sig_witness_expr name (ml_ty : ml_type) =
  match ml_ty with
  | Miniml.Tglob (r, (Miniml.Tglob (w, _, _) :: _), _)
    when Table.is_custom_scalar_ref w ->
    if Table.is_custom r then Some name
    else
      let cname =
        match r with
        | GlobRef.IndRef ind ->
          ctor_struct_name_of_ref ~fallback_idx:0
            (GlobRef.ConstructRef (ind, 1))
        | _ -> ""
      in
      Some
        (name ^ "." ^ Id.to_string (Common.lookup_ctor_field_name ~owner:r cname 0))
  | _ -> None

(** Run [f] in the itree extraction mode that [ty]'s codomain calls for,
    restoring the enclosing mode afterwards.  Reified mode preserves [itree E R]
    as [shared_ptr<ITree<R>>]; sequential mode erases it to [R].  A codomain
    with no monad leaves the mode alone.

    Must wrap type conversion as well as body generation: void-ification and
    [reify_monadic_param_type] (called from [convert_ml_type_to_cpp_type]) both
    read the mode.  We detect reified by the monad template mentioning "ITree",
    e.g. ["std::shared_ptr<ITree<%t1>>"]. *)
let with_itree_mode_for ty f =
  match extract_monad_from_codomain ty with
  | Some monad_ref ->
    with_itree_mode (if is_monad_reified monad_ref then Reified else Sequential) f
  | None -> f ()

(** A class-typed parameter is not a value in C++: the class is a concept, and
    the instance satisfying it is a type.  Such a parameter therefore leaves the
    value parameter list and becomes one of the function's own template
    parameters, named as an instance parameter is -- which is the name every use
    of it ([_tcI0::width()]) and every call site already spell.

    Returns the parameters with the class-typed ones renamed in place, so that
    de Bruijn indices still line up, together with what each takes as a template
    parameter: its kind, its name, the class it instantiates, and the name the
    Rocq binder had. *)
let promote_typeclass_params (params : (Id.t * ml_type) list) =
  let counter = ref 0 in
  let temps = ref [] in
  let params =
    List.map
      (fun (id, ty) ->
        if not (Table.is_typeclass_type ty) then (id, ty)
        else
          let i = !counter in
          counter := i + 1;
          let instance_name = tc_instance_id i in
          (* A unary concept can be written inline ([Params _tcI0]), so the
             compiler enforces it.  A multi-parameter concept cannot: its extra
             type arguments are not in scope where the template parameter is
             declared. *)
          let tt =
            match ty with
            | Miniml.Tglob _ as ty ->
              Option.get (concept_constraint_of_class_type ty)
            | _ ->
              (* Unreachable: [Table.is_typeclass_type] only holds of a
                 [Tglob]. *)
              CErrors.anomaly
                (Pp.str
                   "gen_decls: type-class instance parameter whose type is not \
                    a global reference")
          in
          let class_info =
            match ty with
            | Miniml.Tglob (class_ref, type_args, _) -> Some (class_ref, type_args)
            | _ -> None
          in
          temps := (tt, instance_name, class_info, id) :: !temps;
          (instance_name, ty) )
      params
  in
  (params, List.rev !temps)

(** Generate a C++ function definition from an ML function body.

    When the body has fewer lambda binders than the ML type's domain (i.e. it
    is under-applied), missing parameters are eta-expanded by synthesising
    [MLrel] arguments.  [Tdummy]-typed entries in the missing list are skipped:
    they represent erased type parameters (e.g. [A : Type] in
    [apply : forall A, A -> A]) that have no C++ runtime representation.
    Including them would produce a spurious [CPPabort "unreachable"] IIFE as an
    extra argument, causing [std::function] call sites to receive the wrong
    number of arguments.

    @param n     the global reference for the function being defined
    @param b     the ML AST body
    @param cty   the C++ type of the function (decomposed internally into domain
                 and codomain)
    @param ty    the original ML type (used for domain decomposition and type
                 inference)
    @param temps template type parameters *)
let gen_dfun n b cty ty temps =
  let dom, cod =
    match cty with Tfun (d, c) -> (d, c) | t -> ([ Tvoid ], t)
  in
  (* Suppress __attribute__((pure)) for functions whose ML return type is
     monadic — these perform side effects even though the C++ return type
     may look pure after type erasure. *)
  let no_pure = is_monadic_ml_type (ml_codomain ty) || ast_may_throw b in
  let temps, inner, env =
    with_itree_mode_for ty @@ fun () ->
  (* Void-ify unit codomain: unit as return type maps to C++ void.
     Check the ML result type (unwrapping monad if present) to determine
     if the function returns unit. Then recursively replace the unit enum
     with Tvoid in the C++ codomain type.
     - Sequential mode: Unit → void directly (the monad wrapper is erased,
       so the C++ function literally returns void)
     - Reified mode: Tglob(itree, [E; Unit]) → Tglob(itree, [E; void])
       (printed as shared_ptr<ITree<void>> via monad template) *)
  let unit_void = ml_type_is_void_call ty in
  let cod = apply_unit_void unit_void cod in
  (* Reversed: the lambda collection below peels the innermost arrow first. *)
  let mldom = List.rev (Ml_type_util.ml_domains ty) in
  (* Limit lambda collection to the number of type arrows. When a type alias
     like [State S A = S -> A * S] is used as a return type, the extraction may
     fully uncurry the body (producing more lambdas than the type has arrows),
     but the type [ty] preserves the alias. We must only collect as many lambdas
     as the type has domain arrows, leaving the rest in the body as returned
     closures (C++ lambdas). *)
  let n_type_dom = List.length mldom in
  let all_ids, inner_b = collect_lams b in
  let ids, b =
    if List.length all_ids > n_type_dom then
      let n_excess = List.length all_ids - n_type_dom in
      let kept_ids = List.skipn n_excess all_ids in
      let excess_ids = safe_firstn n_excess all_ids in
      (kept_ids, named_lams excess_ids inner_b)
    else
      (all_ids, inner_b)
  in
  (* get_missing computes the types for eta-expansion parameters. mldom contains
     domain types in reversed order (innermost type first). ids contains
     explicit lambdas in reversed order (innermost lambda first).

     The explicit lambdas bind the OUTERMOST types (at the END of mldom). The
     missing parameters should have the INNERMOST types (at the START of mldom).

     Example: For type R -> nat -> nat -> nat with body λr. <match>: mldom =
     [nat; nat; R] (innermost nat is first, outermost R is last) ids = [(r, R)]
     (one lambda binding the outermost type R) missing types = [nat; nat] (the
     first 2 elements of mldom)

     The old code consumed from HEAD of both lists, incorrectly pairing the
     innermost type (nat) with the outermost lambda (r), causing eta-expansion
     parameters to get wrong types. *)
  let get_missing d a =
    let n_missing = max 0 (List.length d - List.length a) in
    safe_firstn n_missing d
  in
  let missing_types = get_missing mldom ids in
  let n_miss = List.length missing_types in
  (* Assign names so that _x0 gets the outermost missing type (closest to the
     explicit lambdas) and _x(n-1) gets the innermost (= last source param).
     get_missing returns types innermost-first from mldom, so index i maps to
     name _x(n_miss - 1 - i). The resulting list is already in de Bruijn order
     (innermost first) because mapi iterates innermost-first. *)
  let missing =
    List.mapi (fun i t -> (Id (eta_param_id (n_miss - 1 - i)), t)) missing_types
  in
  (* Unify body lambda parameter types with the function signature types.

     When optimize_fix (mlutil.ml) promotes a polymorphic let-fix into a
     top-level Dfix, the body's lambda parameter types may still contain
     unresolved Tmeta cells left over from extraction. For example:

     Definition local_length {A} (l : list A) : nat := let fix go (xs : list A)
     := ... in go l.

     After optimize_fix, the outer function IS the fixpoint, but the lambda
     parameter type for [xs] still holds the original unresolved meta for A,
     while the function's signature type [ty] correctly has Tvar 1 for A.
     Without unification, convert_ml_type_to_cpp_type maps the unresolved meta
     to Tany (std::any), producing e.g. list<std::any> instead of list<T1>.

     By unifying each body parameter type with the corresponding signature type
     via try_mgu, we resolve the shared Tmeta cells in-place. Because metas are
     mutable references shared across the entire body AST, this single
     unification step also fixes every other occurrence of the same meta inside
     the function body (match annotations, recursive calls, etc.). *)
  let n_missing = List.length missing in
  let sig_types_for_ids =
    List.of_seq (Seq.drop n_missing (List.to_seq mldom))
  in
  let rec unify_param_types body_params sig_types =
    match (body_params, sig_types) with
    | (id, body_ty) :: rest_params, sig_ty :: rest_sig ->
      (try try_mgu body_ty sig_ty with _ -> ());
      (id, body_ty) :: unify_param_types rest_params rest_sig
    | _ -> body_params
  in
  let ids = unify_param_types ids sig_types_for_ids in
  (* Replace Tunresolved in body param types with corresponding sig types. This
     handles promoted dependent records where the lambda's type annotation has
     Tunresolved for the erased carrier, while the function signature has
     Tglob(m_carrier, []) which can be resolved by
     convert_ml_type_to_cpp_type. *)
  let rec merge_unknown body_ty sig_ty =
    match (body_ty, sig_ty) with
    | Miniml.Tunknown, _ -> sig_ty
    | Miniml.Tglob (r1, ts1, a1), Miniml.Tglob (r2, ts2, _)
      when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
      Miniml.Tglob (r1, List.map2 merge_unknown ts1 ts2, a1)
    | Miniml.Tarr (t1a, t1b), Miniml.Tarr (t2a, t2b) ->
      Miniml.Tarr (merge_unknown t1a t2a, merge_unknown t1b t2b)
    | _ -> body_ty
  in
  let ids =
    if List.length ids = List.length sig_types_for_ids then
      List.map2
        (fun (id, body_ty) sig_ty -> (id, merge_unknown body_ty sig_ty))
        ids
        sig_types_for_ids
    else
      ids
  in
  (* Replace body lambda types with signature types for env_types tracking, but
     ONLY when the signature type has fewer arrows than the body type. This
     handles type aliases like [State S A = S -> A * S] where expansion adds
     extra arrows. Using signature types in env_types ensures that inner call
     sites can detect over-application and generate chained calls (e.g. f(a)(s')
     instead of f(a, s')). We must NOT replace unconditionally, because that
     would make parameter types in the .cpp definition differ from the .h
     declaration (which uses gen_sfun with expanded types). *)
  (* Nor where the signature names a type alias that takes promoted
     parameters -- [FusedS := state * ...] under [Existing Instance], declared
     [template <typename ptr>].  Its body names class fields only the alias's
     own parameters resolve, so the expansion the lambda's binder carries
     spells them erased, and the alias is the only spelling that keeps them;
     the header's [gen_sfun] reads the signature's types already. *)
  let promoted_alias t =
    match Mlutil.type_simpl t with
    | Miniml.Tglob ((GlobRef.ConstRef _ as g), _, _) ->
      Table.promoted_type_params g <> []
    | _ -> false
  in
  let ids =
    if List.length ids = List.length sig_types_for_ids then
      List.map2
        (fun (id, body_ty) sig_ty ->
          if count_ml_arrows body_ty > count_ml_arrows sig_ty
             || promoted_alias sig_ty
          then
            (id, sig_ty)
          else
            (id, body_ty) )
        ids
        sig_types_for_ids
    else
      ids
  in
  let tvar_subst_from_sig =
    if not (has_tvar ty)
       && List.length ids = List.length sig_types_for_ids then
      let rec chase = function
        | Miniml.Tmeta {contents = Some t} -> chase t
        | t -> t
      in
      let rec collect body_ty sig_ty acc =
        let body_ty = chase body_ty in
        let sig_ty = chase sig_ty in
        match (body_ty, sig_ty) with
        | (Miniml.Tvar (_, i)), _
          when not (has_tvar sig_ty) ->
          if List.mem_assoc i acc then acc else (i, sig_ty) :: acc
        | Miniml.Tglob (r1, ts1, _), Miniml.Tglob (r2, ts2, _)
          when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
          List.fold_left2 (fun acc a b -> collect a b acc) acc ts1 ts2
        | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) ->
          collect a1 a2 (collect b1 b2 acc)
        | _ -> acc
      in
      let direct = List.fold_left2
        (fun acc (_, body_ty) sig_ty -> collect body_ty sig_ty acc)
        [] ids sig_types_for_ids in
      if direct <> [] then direct
      else begin
        let all_body = List.map (fun (_, ty) -> ty) ids in
        let rec cross t1 t2 acc =
          let t1 = chase t1 in
          let t2 = chase t2 in
          match (t1, t2) with
          | (Miniml.Tvar (_, i)), _
            when not (has_tvar t2) ->
            if List.mem_assoc i acc then acc else (i, t2) :: acc
          | Miniml.Tglob (r1, ts1, _), Miniml.Tglob (r2, ts2, _)
            when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
            List.fold_left2 (fun acc a b -> cross a b acc) acc ts1 ts2
          | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) ->
            cross a1 a2 (cross b1 b2 acc)
          | _ -> acc
        in
        let pairs = List.concat_map (fun t1 ->
          List.concat_map (fun t2 ->
            if t1 == t2 then [] else cross t1 t2 []
          ) all_body
        ) all_body in
        List.fold_left (fun acc (i, t) ->
          if List.mem_assoc i acc then acc else (i, t) :: acc
        ) [] pairs
      end
    else
      []
  in
  let ids, b =
    match tvar_subst_from_sig with
    | [] -> (ids, b)
    | subst ->
      let apply_subst ty = subst_tvars_type subst ty in
      ( List.map (fun (id, ty) -> (id, apply_subst ty)) ids,
        map_types_in_ast apply_subst b )
  in
  (* Extraction numbers a type variable inside a body by the position of its
     binder among *all* the leading binders, while the recorded type numbers it
     among the type binders only.  A value binder that comes before a type
     binder -- a type-class instance, or [hk_map]'s [map_f] -- therefore shifts
     everything after it, and the body would name a template parameter that
     stands for something else.  Rebuild the correspondence from the binder
     kinds and put the body on the signature's numbering, which is the one the
     template parameters are named for.  The parameter types in [ids] have
     already been reconciled with the signature above, so only the body needs
     it.  The map is the identity whenever no value binder comes first, which
     is the common case. *)
  let b =
    let _, n_type_binders, renumbering =
      List.fold_left
        (fun (pos, rank, acc) dom ->
          match dom with
          | Miniml.Tdummy Miniml.Ktype ->
            let acc =
              if pos = rank then acc else (pos, Miniml.Tvar (Schematic, rank)) :: acc
            in
            (pos + 1, rank + 1, acc)
          | _ -> (pos + 1, rank, acc) )
        (1, 1, [])
        (Ml_type_util.ml_domains (try Table.find_type n with Not_found -> ty))
    in
    let n_type_binders = n_type_binders - 1 in
    (* Extraction does not always fall out of step: when the body happens to
       have been numbered against the type binders alone it is already right,
       and renumbering it again would move a variable off its own template
       parameter.  The one observable symptom of the mismatch is the body
       naming an index past the last type binder, which the signature
       numbering cannot produce, so take that as the trigger. *)
    let body_max =
      let m = ref 0 in
      ignore
        (map_types_in_ast
           (fun ty ->
             m := max !m (Mlutil.type_maxvar ty);
             ty )
           b);
      !m
    in
    (* An index past the last type binder is not proof on its own: a
       pattern's existential -- [VisF]'s answer type, numbered after the
       enclosing ones -- is one too.  A body numbered by position never names
       a value binder's position, though, so one that does is already on the
       signature's numbering. *)
    let value_positions =
      List.mapi (fun i dom -> (i + 1, dom))
        (Ml_type_util.ml_domains (try Table.find_type n with Not_found -> ty))
      |> List.filter_map (fun (i, dom) ->
             match dom with Miniml.Tdummy Miniml.Ktype -> None | _ -> Some i)
    in
    let names_a_value_position =
      let rec mentions t =
        match t with
        | Miniml.Tvar (_, i) -> List.mem i value_positions
        | Miniml.Tapp (i, l) -> List.mem i value_positions || List.exists mentions l
        | Miniml.Tglob (_, l, _) -> List.exists mentions l
        | Miniml.Tarr (a, c) -> mentions a || mentions c
        | Miniml.Tmeta {contents = Some t} -> mentions t
        | _ -> false
      in
      let found = ref false in
      ignore
        (map_types_in_ast
           (fun ty ->
             if mentions ty then found := true;
             ty )
           b);
      !found
    in
    let renumbering =
      if body_max > n_type_binders && not names_a_value_position then renumbering
      else []
    in
    match renumbering with
    | [] -> b
    | subst -> map_types_in_ast (subst_tvars_type subst) b
  in
  (* Detect which function-typed parameters are NOT simply forwarded at
     self-recursive call sites.  These are excluded from template-parameter
     promotion below — they keep their [Tconst (Tfun(dom, cod))] type
     which prints as [const std::function<R(Args...)>].

     [detect_non_forwarded_params] returns source-order indices (param 0 =
     first Rocq parameter).  The parameter list [ids] is in de Bruijn order
     (innermost first), so a loop over it asks about source index
     [List.length ids - 1 - i] -- the length of the list it is iterating,
     which by then also holds the eta-expanded parameters. *)
  let non_fwd_param_indices = detect_non_forwarded_params n (List.length ids) b in
  (* A callable a closure holds on to is not generalised either: it arrives
     as a [crane::fn], so every capture shares it rather than copying the
     caller's closure. *)
  let escaping =
    escaping_params
      ~suspended:(Table.is_coinductive_type (ml_return_type ty))
      (List.length ids) b
  in
  let non_fwd_set = IntSet.of_list (escaping @ non_fwd_param_indices) in
  let is_non_fwd_param_source i = IntSet.mem i non_fwd_set in
  let all_params = missing @ ids in
  (* Type class instance parameters become C++ template type parameters. We
     assign unique names (_tcI0, _tcI1, ...) to avoid collision with: - User
     variable names like 'i', 'j', etc. - Other generated names in the same
     scope The original parameter order is preserved for correct de Bruijn
     indexing. *)
  let all_params_for_env, typeclass_temps =
    promote_typeclass_params
      (List.map
         (fun (ml_id, ty) -> (cpp_id_of_id (id_of_mlid ml_id), ty))
         all_params )
  in
  (* Build a substitution map for PROMOTED TYPE VARIABLES: fields that were
     promoted from record values to type parameters during concept generation.

     When a function takes a typeclass parameter, references to that typeclass's
     promoted fields must be qualified as types (typename _tcI0::field), not
     accessed as values (_tcI0->field).

     Example:
       Coq function:
         Fixpoint mfold (M : Monoid) (l : list (m_carrier M)) : m_carrier M

       Extraction intermediate form:
         ML type has [Tglob(m_carrier, [])] ← marked as promoted type var
         Converts to [Tpromoted "m_carrier"] ← needs resolution

       This map provides the resolution:
         "m_carrier" ↦ Tqualified(Tvar(0, Some "_tcI0"), "m_carrier")
         Which prints as: typename _tcI0::m_carrier

     For nested typeclasses (e.g., PreStableCategory has a base_category : PreCategory),
     promoted vars are doubly qualified:
       "Obj" ↦ typename _tcI0::base_category::Obj

     The map is applied by [resolve_promoted_in_type] to substitute all
     [Tpromoted] markers with their qualified forms. *)
  let promoted_var_resolutions =
    List.concat_map
      (fun (_tt, tc_name, class_info, _) ->
        match class_info with
        | Some (class_ref, _) ->
          promoted_resolutions class_ref (Tinstance (tc_name, class_ref))
        | None -> [] )
      typeclass_temps
  in
  let hkt_tvar_resolutions = hkt_tvar_resolutions_of_type ty in
  (* Type annotations inside the body must name the same resolved types as the
     signature does. *)
  let gen_body_stmts env cw e =
    apply_hkt_resolutions_stmts hkt_tvar_resolutions (gen_stmts env cw e)
  in
  (* Substitute promoted type var markers [Tpromoted name] with their
     qualified resolutions throughout a C++ type tree. *)
  let resolve_promoted_in_type =
    rewrite_cpp_type (function
      | Tvar (Tv_index (i, _)) when List.mem_assoc i hkt_tvar_resolutions ->
        Some (List.assoc i hkt_tvar_resolutions)
      | Tpromoted name as ty ->
        Some
          ( match
              List.find_opt
                (fun (n, _) -> Id.equal n name)
                promoted_var_resolutions
            with
          | Some (_, resolved) -> resolved
          | None -> ty )
      | _ -> None )
  in
  (* Apply promoted var resolution to domain and codomain types *)
  let has_type_resolutions =
    promoted_var_resolutions <> [] || hkt_tvar_resolutions <> []
  in
  let dom =
    if has_type_resolutions then
      List.map resolve_promoted_in_type dom
    else dom
  in
  let cod =
    if has_type_resolutions then resolve_promoted_in_type cod else cod
  in
  (* Push params into environment for de Bruijn lookup during body generation.
     collect_lams returns params in reverse order (innermost first), so MLrel 1
     refers to the last param in the list.

     push_vars' may rename parameters to avoid collisions. For example, if Rocq
     has: fun (f : T) (f0 : F) (f : forest) => ... push_vars' renames the
     duplicate 'f' to 'f1', producing: [f; f0; f1]

     We must use these renamed ids (all_ids) for both: 1. The environment (for
     correct de Bruijn lookup in the body) 2. The C++ function signature (so
     parameter names match body references)

     Previously, the code discarded all_ids and used original names for the
     signature, causing mismatches like: void foo(T f, F f0, forest f) { ...
     f1->v() ... } where 'f1' in the body didn't match any parameter name. *)
  let all_ids, env = push_vars' all_params_for_env (empty_env ()) in
  reset_env_types ();
  push_binders env all_ids;
  let n_params = List.length all_params in
  let owned_flags = infer_owned_flags n_params b all_ids in
  (* Zip all_ids with ownership flags. all_ids and all_params have the same
     length (push_vars' preserves length), so owned_flags aligns 1:1. *)
  let all_ids_with_owned =
    List.map2 (fun (id, ty) owned -> (id, ty, owned)) all_ids owned_flags
  in
  (* For function signature, use renamed ids but exclude typeclass, void,
     and skipped-type params (e.g. ReSum instances from the ITree library
     that are not recognized by is_typeclass because ReSum's GlobRef is a
     ConstRef, not an IndRef registered in inductive_kinds). *)
  let ids_with_owned =
    List.filter
      (fun (_, ty, _) ->
        (not (Table.is_typeclass_type ty))
        && not (ml_type_is_void ty)
        && not (is_skipped_ml_type ty) )
      all_ids_with_owned
  in
  (* Convert ML types to C++ types and wrap with const. Owned shared_ptr params:
     pass by value (shared_ptr<T>) Borrowed shared_ptr params: pass by const ref
     (const shared_ptr<T>&) *)
  let ids =
    List.map
      (fun (x, ty, owned) ->
        let cpp_ty = convert_ml_type_to_cpp_type env [] ty in
        let cpp_ty =
          if has_type_resolutions then resolve_promoted_in_type cpp_ty
          else cpp_ty
        in
        (* Reify monadic parameter types: itree E R → shared_ptr<ITree<R>> *)
        let cpp_ty = reify_monadic_param_type ty cpp_ty in
        let wrapped = wrap_param_by_ownership ~is_owned:owned cpp_ty in
        (x, wrapped) )
      ids_with_owned
  in
  (* Promote forwarded function-typed parameters to C++ template parameters.

     Function-typed parameters (those with C++ type [Tconst (Tfun(...))])
     are normally promoted to template parameters with [std::is_invocable_v]
     requires-clause constraints.  This replaces [const std::function<R(Args...)>]
     with a template type variable [F&&], giving the compiler the exact lambda
     type so it can inline the call body — no type-erasure overhead.

     For example, [tree_rect]'s two function parameters become:

       template <typename F0, typename F1>
         requires std::is_invocable_v<F0 &, unsigned int &>
               && std::is_invocable_v<F1 &, shared_ptr<tree> &, T1 &, ...>
       static T1 tree_rect(F0 &&f, F1 &&f0, ...);

     This works for [tree_rect] because its recursive calls pass [f] and
     [f0] unchanged — the template type stays the same at every recursion
     depth.

     Non-forwarded parameters are excluded from this promotion.  A parameter
     that receives a *different* expression at a recursive call site means the
     template type would be different at each recursion depth, causing
     infinite template instantiation.  These parameters keep their
     [const std::function<R(Args...)>] type, which is a concrete
     (non-template) type that stays the same regardless of wrapping.

     For example, [partition_cps p l k] has three parameters:
     - [p] is forwarded unchanged to the recursive call → template [F0 &&p]
     - [l] is not function-typed → stays as-is
     - [k] receives a different expression at the recursive call → [const std::function<...> k]

     This loop iterates [List.rev ids] which is in source order,
     so we use [is_non_fwd_param_source] for the guard. *)
  (* Determine which tvars are "primary" — deducible from non-function domain
     params or the return type.  Function-typed params that reference tvars
     outside this set (e.g., erased HKT type variables) get TTtypename (no
     is_invocable_v constraint) instead of TTfun, to avoid referencing template
     type parameters that were filtered out as phantom by gen_decl_for_pp. *)
  let primary = primary_tvar_indices dom cod in
  let unwrap_fun_ty2 = function
    | Tconst ((Tfun _ as f)) | Tref (Lvalue, Tconst (Tfun _ as f)) -> Some f
    | Tfun _ as f -> Some f
    | _ -> None
  in
  (* A parameter whose function type erased to [std::any] throughout, in a
     signature that deduces no type variable at all, is not worth generalising:
     the deduced callable pins nothing down, and the template it forces costs
     the definition its usability as a value of the type its Rocq signature
     names ([church]). *)
  let is_erased_fun_param ty =
    IntSet.is_empty primary
    &&
    match unwrap_fun_ty2 ty with
    | Some f -> Ml_type_util.is_fully_erased_fun_ty f
    | None -> false
  in
  let fun_tys =
    List.filter_map
      (fun (x, ty, i) ->
        match unwrap_fun_ty2 ty with
        | Some (Tfun (fdom, fcod))
          when (not (is_non_fwd_param_source i)) && not (is_erased_fun_param ty)
          ->
          let fun_idx = get_tvar_indices (Tfun (fdom, fcod)) in
          let has_undeclared =
            List.exists (fun idx -> not (IntSet.mem idx primary)) fun_idx
          in
          if has_undeclared then
            Some (x, TTtypename, fun_tparam_id i)
          else
            let fcod = if is_cpp_unit_type fcod then Tvoid else fcod in
            Some (x, TTfun (fdom, fcod), fun_tparam_id i)
        | _ -> None )
      (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids))
  in
  (* Replace the parameter type of promoted (forwarded) function params with the
     template type variable [F&&]. Non-forwarded params are left untouched — they
     keep [Tconst (Tfun(dom, cod))] which prints as [const
     crane::fn<R(Args...)>]. This loop iterates [ids] in de Bruijn order. *)
  let ids =
    List.mapi
      (fun i (x, ty) ->
        match unwrap_fun_ty2 ty with
        | Some (Tfun _)
          when (not (is_non_fwd_param_source (List.length ids - i - 1)))
               && not (is_erased_fun_param ty) ->
          ( x,
            Tref (Forwarding, named_tvar (fun_tparam_id (List.length ids - i - 1))) )
        | _ -> (x, ty) )
      ids
  in
  (* A parameter whose type is a callable behind a type alias -- a one-method
     class demoted to [template <template <typename> class T> using C =
     std::function<...>] -- is one no argument can be deduced through: what
     arrives is a lambda, a lambda never has the alias's type, and deduction
     fails before the conversion that would have succeeded is considered.

     Taking it out of deduction is what lets the conversion happen.  The
     alternative, generalising it to an [F &&] the way a bare [Tfun] parameter
     is generalised above, would add a template parameter and so shift every
     explicit argument list that already names this function -- and there is
     nothing to gain by deducing a type the alias's own arguments, pinned by
     the other parameters, already determine. *)
  let ids =
    (* A type constructor standing in for a template parameter: the alias is
       applied to something of kind [Set -> Set], so the alias itself takes a
       [template <typename> class] parameter -- the shape C++ cannot deduce. *)
    let rec is_hk_arg a =
      match a with
      | Ttyctor _ -> true
      | Tapply (Tvar _, _) -> true
      | Tconst t | Tref (_, t) -> is_hk_arg t
      | _ -> false
    in
    (* The alias stands for a callable.  A struct behind an alias deduces
       perfectly well; it is only [std::function] that a lambda argument cannot
       match. *)
    let alias_rhs_is_fun kn =
      match Table.lookup_typedef_unchecked kn with
      | Some ml_ty -> (
        match convert_ml_type_to_cpp_type env [] ml_ty with
        | Tfun _ | Tconst (Tfun _) -> true
        | _ -> false )
      | None -> false
    in
    (* Whatever its arguments: a definitional class -- [Cat<T1, T2>], an
       alias for [std::function<...>] -- names this function's parameters, and
       a lambda argument cannot be matched against it.  A call site reads the
       same parameter as no source of deduction ([deducible_tvars_of_glob]),
       so the two agree on what has to be written. *)
    let rec alias_hides_fun ty =
      match ty with
      | Tconst t | Tref (_, t) -> alias_hides_fun t
      | Tapply (Tglob (GlobRef.ConstRef kn, [], _), args)
       |Tglob (GlobRef.ConstRef kn, (_ :: _ as args), _) ->
        (List.exists is_hk_arg args || get_tvar_indices ty <> [])
        && alias_rhs_is_fun kn
      | _ -> false
    in
    (* A callable parameter the recursion could not forward keeps its
       [std::function] spelling, and that is not a fallback: the type erasure
       is what makes the recursion close.  Rebuilding the callable at each step
       gives a new closure type at each step, so an [F &&] would instantiate a
       fresh specialisation forever.  But the spelling names this function's
       own template parameters, and a lambda argument never has that type --
       so the same deduction failure as the alias above, for the same reason,
       and the same repair.  Where the type names no parameter there is
       nothing to deduce and nothing to shield. *)
    let rec spelled_fun_is_deduced_against ty =
      match ty with
      | Tconst t | Tref (_, t) -> spelled_fun_is_deduced_against t
      | Tfun _ -> get_tvar_indices ty <> []
      | _ -> false
    in
    (* The wrapper the ownership pass put on stays where it is; only the type
       it wraps is taken out of deduction. *)
    let rec at_core f ty =
      match ty with
      | Tconst t -> Tconst (at_core f t)
      | Tref (k, t) -> Tref (k, at_core f t)
      | t -> f t
    in
    List.map
      (fun (x, ty) ->
        if alias_hides_fun ty || spelled_fun_is_deduced_against ty then
          ( x,
            at_core
              (fun t -> Tnondeduced t)
              ty )
        else (x, ty) )
      ids
  in
  (* Add type class instance template parameters - instance types come first *)
  let typeclass_temps_basic =
    (* A constraint's arguments are types like any other and get the same
       resolution the signature does: [ToDvalueBase<_tcI0, T1, ptr, iptr>]
       spells the two promoted variables bare, and bare is the file-scope
       [std::any] rather than the [Params] instance standing beside it. *)
    List.map
      (fun (tt, id, _, _) ->
        let tt =
          match tt with
          | TTconcept (r, (_ :: _ as args)) when has_type_resolutions ->
            TTconcept (r, List.map resolve_promoted_in_type args)
          | tt -> tt
        in
        (tt, id) )
      typeclass_temps
  in
  (* Build recursive call reference with typeclass and type params only.
     Function type params (from fun_tys) are excluded because they should be
     deduced from arguments, not explicitly specified in recursive calls. *)
  (* A function recursing over a nested (non-uniform) inductive is
     polymorphically recursive: the self-call is at [nest (A * A)], not at
     [nest A].  Repeating the enclosing template arguments would force the
     wrong instantiation, so let C++ deduce them from the argument instead —
     the recursive argument always mentions the inductive, so deduction
     succeeds. *)
  let recurses_on_non_uniform_ind =
    let rec mentions = function
      | Tglob (r, args, _) | Tnamespace (r, Tglob (_, args, _)) ->
        Table.is_non_uniform_inductive r || List.exists mentions args
      | Tconst t | Tnamespace (_, t) | Tref (_, t) | Tshared_ptr t -> mentions t
      | Tfun (d, c) -> List.exists mentions d || mentions c
      | _ -> false
    in
    List.exists (fun (_, ty) -> mentions ty) ids
  in
  (* ... unless the type parameters are erased out of the signature entirely
     (the inductive is rendered with [std::any] fields and the function takes
     no function-typed argument to name them).  Then no argument mentions
     them and deduction has nothing to work from -- but nothing in the body
     reads them either, so the self-call passes the enclosing parameters
     straight through.  That keeps the recursion to a single instantiation,
     and, unlike defaulting them, still rejects a caller that supplies
     nothing. *)
  let tvars_are_phantom = recurses_on_non_uniform_ind && fun_tys = [] in
  let rec_call_temps =
    if recurses_on_non_uniform_ind && not tvars_are_phantom then
      typeclass_temps_basic
    else
      typeclass_temps_basic
      @ List.filter
          (fun (_, id) ->
            not (List.exists (fun (i, _) -> tvar_id i = id) hkt_tvar_resolutions) )
          temps
  in
  let rec_call =
    mk_cppglob n (List.map (fun (_, id) -> named_tvar id) rec_call_temps)
  in
  (* Combine all template params for function signature. Save the non-typeclass
     type params for Tvar index resolution below. *)
  let regular_temps = temps @ List.map (fun (_, t, n) -> (t, n)) fun_tys in
  (* Variables standing for a higher-kinded class parameter are rendered as
     associated types of the instance, so they must not also be declared as
     template parameters: nothing would deduce them.  They stay in
     [regular_temps] below, which only feeds Tvar index resolution. *)
  let is_hkt_temp (_, id) =
    List.exists (fun (i, _) -> tvar_id i = id) hkt_tvar_resolutions
  in
  let temps =
    typeclass_temps_basic
    @ List.filter_map
        (fun t ->
          if is_hkt_temp t then None else Some t )
        regular_temps
  in
  (* Requires clause for typeclass constraints not yet implemented. *)
  (* Set current type variables for pattern matching lambda generation.
     These are the template parameters that can be used in type annotations.
     Exclude typeclass instance params — they are not ML type variables
     and should not participate in Tvar index resolution. ML Tvar indices
     (Tvar 1, Tvar 2, ...) correspond to regular type params only. *)
  let type_var_ids =
    List.filter_map
      (fun (tt, id) ->
        match tt with
        | TTtypename | TTtypename_default _ | TTtemplate _ -> Some id
        | _ -> None )
      regular_temps
  in
  set_current_type_vars type_var_ids;
  (* The head itself, at the kinds it declares: see
     {!Translation_state.current_template_head}. *)
  let saved_template_head = get_current_template_head () in
  set_current_template_head (typeclass_temps_basic @ regular_temps);
  set_current_param_types all_ids;
  (* Activate promoted var resolution for body generation — types like
     [Tpromoted "Obj"] in type annotations will be resolved to
     qualified access through the typeclass instance chain. *)
  let saved_promoted_var_map = (!tctx).promoted_var_map in
  (* Extend, never replace.  This declaration's own instance parameters answer
     first -- a variable they declare is the one the body is written in -- but
     what {!with_body_resolutions} read from the body and from the declarations
     it names is the only answer a function with no instance parameter of its
     own has.  [check : unit -> nat] whose body applies [@runS (@ParamsV
     natIPtr)] has none, and replacing the map dropped the answer on the way
     in, so the body spelled the file-scope erased alias in a scope that knew
     the instance perfectly well. *)
  tctx :=
    { !tctx with
      promoted_var_map = promoted_var_resolutions @ saved_promoted_var_map };
  (* Name the declaration being generated: inner fixpoints lifted out of it
     take their identity from it. *)
  let saved_decl_ref = !Table.current_decl_ref in
  Table.current_decl_ref := Some n;
  (* A coinductive value is suspended at its constructors (see
     [suspend_ctor]); the body around them runs where it is called.  Only a
     body that calls itself outside every constructor -- guarded, for Rocq,
     only up to unfolding -- is suspended whole. *)
  let ml_ret = ml_return_type ty in
  let is_cofix_return =
    Table.is_coinductive_type ml_ret && calls_eagerly n b
  in
  let cofix_wrap x =
    if is_cofix_return then
      let ret_cpp = cod in
      let coind_ref =
        match ml_ret with
        | Miniml.Tglob (r, _, _) -> r
        | _ ->
          CErrors.anomaly
            (Pp.str "gen_decl: cofixpoint return type expected to be Tglob")
      in
      let type_args =
        match ml_ret with
        | Miniml.Tglob (_, args, _) ->
          List.map
            (fun t ->
              convert_ml_type_to_cpp_type env type_var_ids t )
            args
        | _ -> []
      in
      let lazy_factory =
        CPPscope (mk_cppglob coind_ref type_args, Id.of_string "lazy_", [])
      in
      let thunk = mk_lambda [] (Some ret_cpp) [Sreturn (Some x)] ~capture:Closure in
      Sreturn (Some (mk_call lazy_factory [thunk]))
    else if cod = Tvoid then
      (* void function: execute expression for side effects, then return.
         Some tail expressions (like writeTVar) have side effects that must
         not be discarded. Skip pure expressions (variables, enum values,
         inline-custom literals like std::monostate{}) to avoid dead-code
         warnings. *)
      ( match x with
      | CPPenum_val _ | CPPvar _ | CPPint _ | CPPfloat _ | CPPraw _ ->
        Sreturn None
      | CPPglob (_, _, Some ci) when ci.ci_inline <> None -> Sreturn None
      | _ -> Sblock [Sexpr x; Sreturn None] )
    else
      Sreturn (Some x)
  in
  (* Generate sigma type precondition assertions *)
  let sigma_asserts =
    let assertions = Table.get_sigma_assertions n in
    if assertions = [] then
      []
    else
      let all_id_arr = Array.of_list (List.rev all_ids) in
      (* outermost param first; [all_params] runs in the same order and
         carries the ML types, which say whether a parameter is a [sig]. *)
      let all_ml_arr = Array.of_list (List.rev all_params) in
      (* A template's placeholders are numbered outwards from the parameter
         the assertion was registered for: [%0] is that parameter's witness,
         [%1] the binder before it, and so on.  Substituting the highest index
         first keeps [%10] from being read as [%1] followed by a digit. *)
      let render param_idx witness_of template =
        let substs =
          List.init (param_idx + 1) (fun k ->
            let name = Id.to_string (fst all_id_arr.(param_idx - k)) in
            ( Printf.sprintf "%%%d" k,
              if k = 0 then witness_of name (snd all_ml_arr.(param_idx - k))
              else Some name ) )
        in
        let substs =
          List.filter_map
            (fun (ph, r) -> Option.map (fun r -> (ph, r)) r)
            substs
        in
        Common.render_template (List.rev substs) template
      in
      (* The assertion holds of the parameter's witness, so it can only be
         made when the witness has an expression; failing that -- and failing
         a placeholder naming a binder outside this parameter's reach -- the
         precondition is reported rather than checked, still spelling the
         parameters it speaks of. *)
      let subst_placeholders param_idx template =
        let stated = render param_idx sig_witness_expr template in
        if String.contains stated '%' then
          Error (render param_idx (fun name _ -> Some name) template)
        else Ok stated
      in
      List.filter_map
        (fun (param_idx, assertion) ->
          if param_idx >= Array.length all_id_arr then
            None
          else
            match
              assertion
            with
            | Table.AssertExpr template ->
              ( match subst_placeholders param_idx template with
              | Ok expr_str -> Some (Sassert (Pchecked expr_str))
              | Error comment -> Some (Sassert (Pstated comment)) )
            | Table.AssertComment comment -> Some (Sassert (Pstated comment)) )
        assertions
  in
  begin_body ();
  (* Phase 2: Initialize owned-variable tracking for move insertion. Parameters
     at de Bruijn indices 1..n_params; owned ones get added to the set. *)
  let n_all_params = List.length all_params in
  tctx := { !tctx with move_n_params = n_all_params };
  tctx :=
    { !tctx with
      move_owned_vars =
          List.fold_left
            (fun acc (i, owned) ->
              if owned then
                let ml_ty = snd (List.nth all_params i) in
                if Escape.is_shared_ptr_type ml_ty
                   || is_nontrivial_value_ml_type ml_ty then
                  Escape.IntSet.add (i + 1) acc
                else acc
              else acc )
            Escape.IntSet.empty
            (List.mapi (fun i o -> (i, o)) owned_flags) };
  tctx := { !tctx with move_dead_after = Escape.IntSet.empty };
  (* Expose the C++ return type to inner call sites so they can recover erased
     template type args (see try_recover_erased_return_type). *)
  let saved_return_type = (!tctx).current_cpp_return_type in
  tctx := { !tctx with current_cpp_return_type = Some cod };
  (* For non-inlined custom constants (axioms mapped via Crane Extract
     Constant), generate a forwarding body that delegates to the custom
     implementation instead of the default CPPabort throw. *)
  let custom_forwarding_body =
    match b with
    | MLaxiom _ when is_custom n && not (to_inline n) ->
      let custom_name = find_custom n in
      let param_vars = List.map (fun (id, _) -> CPPvar id) ids in
      Some [Sreturn (Some (mk_call (CPPraw custom_name) param_vars))]
    | _ -> None
  in
  (* method_self_ns is set by the caller (gen_decl/gen_dfun_def) before
     computing cty, so it's already active here. *)
  let inner =
    if missing == [] then (
      let b =
        match custom_forwarding_body with
        | Some stmts -> stmts
        | None ->
          let b =
            List.map (glob_subst_stmt n rec_call) (gen_body_stmts env cofix_wrap b)
          in
          return_captures_by_value b
      in
      (* State-threading optimization: when the return type is [pair<S, R>]
         and there is a value parameter of type [S], insert [std::move] at
         every recursive self-call and every [make_pair] return so that the
         state value is moved rather than deep-copied at each recursion level.
         This turns O(L * N) total copies into O(L) moves. *)
      let ids, b =
        let rec strip_ns = function Tconst t | Tnamespace (_, t) -> strip_ns t | t -> t in
        match strip_ns cod with
        | Tglob (g, s_ty :: _, _) when is_prod_global g -> (
          match
            List.find_opt
              (fun (_, ty) -> cpp_ty_eq (match ty with Tconst t -> t | t -> t) s_ty)
              ids
          with
          | Some (state_id, _) when state_threads_linearly n state_id b ->
            rewrite_state_threading_moves n state_id s_ty ids b
          | Some _
          | None -> (ids, b) )
        | _ -> (ids, b)
      in
      let guard =
        build_guard_compare_stmts n ids
      in
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfun
        (mk_dfun n ~ret:cod ~no_pure
           (Ddef
              ( ids,
                dead_unit_returns_to_abort cod
                  (erase_returned_fn_values cod (guard @ sigma_asserts @ b)) ) ) ) )
    else
      (* Eta-expansion: the body 'b' references original params starting at
         MLrel 1. After adding k=|missing| new params to the environment, the
         original params are now at indices k+1, k+2, etc. We must lift 'b' by k
         to adjust its references.

         Example: For accessor f : R -> nat -> nat -> nat with body λr. match
         r... - Original body references r as MLrel 1 - After adding 2
         eta-params (_x0, _x1), environment is [_x1; _x0; r] - r is now at index
         3, so we lift b by 2: MLrel 1 -> MLrel 3

         Then we apply the lifted body to the eta-expansion arguments.

         Exception: axiom/exn bodies always throw — applying them to arguments
         produces invalid C++ (calling a void result). Generate the body
         directly. *)
      let b =
        match custom_forwarding_body with
        | Some stmts -> stmts
        | None ->
        match b with
        | MLaxiom _ | MLexn _ ->
          List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap b)
        | _ ->
          let k = List.length missing in
          let lifted_b = ast_lift k b in
          (* Only pass value-typed (non-dummy) eta args to the body.
             Dummy-typed entries in [missing] represent erased type parameters
             (e.g. [A : Type] in [apply : forall A, A -> A]).  Passing
             [MLrel (i+1)] for them would generate a [CPPabort "unreachable"]
             IIFE as an extra argument to a [std::function] field that only
             takes one value argument. *)
          let args = List.rev (List.filter_map
            (fun (i, (_, t)) -> if isTdummy t then None else Some (MLrel (i + 1)))
            (List.mapi (fun i x -> (i, x)) missing)) in
          List.map
            (glob_subst_stmt n rec_call)
            (gen_body_stmts env cofix_wrap (apply_eta_args lifted_b args))
      in
      let b = return_captures_by_value b in
      (* let b = List.map forward_fun_args b in *)
      let guard =
        build_guard_compare_stmts n ids
      in
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfun
        (mk_dfun n ~ret:cod ~no_pure
           (Ddef
              ( ids,
                dead_unit_returns_to_abort cod
                  (erase_returned_fn_values cod (guard @ sigma_asserts @ b)) ) ) )
  in
  tctx := { !tctx with current_cpp_return_type = saved_return_type };
  Table.current_decl_ref := saved_decl_ref;
  tctx := { !tctx with promoted_var_map = saved_promoted_var_map };
  set_current_template_head saved_template_head;
  (* {b Entry point detection for monadic [main].}

     When a Rocq definition named [main] has a monadic return type, it is
     treated as the program entry point.  The generated C++ must provide a
     standard [int main()] — the handling depends on two factors:

     {b 1. Inside a struct} ([struct_name = Some _]):
       The function keeps its original name.  [Struct::main()] does not
       collide with the free [int main()] because C++ member functions
       occupy a separate scope.  A wrapper [int main() \{ Struct::main(); \}]
       is generated by {!Extract_env.print_impl_module} from the
       {!Table.set_main_function} registration.

     {b 2. Top-level, sequential mode} ([struct_name = None, needs_run = false]):
       The monad is erased (sequential ITree mode), so the function body is
       plain imperative C++ returning [void].  Instead of emitting a separate
       [_main] + wrapper, we convert the definition directly into
       [int main()] by changing the return type to [int] and replacing every
       [Sreturn None] (i.e. [return;]) with [Sreturn (Some (CPPint 0))]
       (i.e. [return 0;]).  No wrapper is needed.

     {b 3. Top-level, reified mode} ([struct_name = None, needs_run = true]):
       The function returns [shared_ptr<ITree<R>>] and must be called with
       [->run()] to execute the interaction tree.  We rename the function to
       [_main] (to avoid colliding with the free [int main()]) and register
       it for wrapper generation: [int main() \{ _main()->run(); return 0; \}]. *)
  let inner = match n with
    | GlobRef.ConstRef c ->
      let label_str = Label.to_string (Constant.label c) in
      if label_str = "main" && is_monadic_ml_type (ml_codomain ty) then begin
        let struct_name =
          let mp = Constant.modpath c in
          match mp with
          | ModPath.MPdot (_, l) -> Some (Id.of_string (Label.to_string l))
          | _ -> None
        in
        let needs_run = match resolve_tmeta (ml_codomain ty) with
          | Tglob (r, _, _) -> is_monad_reified r
          | _ -> false
        in
        match struct_name, needs_run with
        | Some _, _ ->
          (* Case 1: inside a struct — keep name, register for wrapper *)
          Table.set_main_function (Id.of_string "main") (ml_codomain ty) struct_name needs_run;
          inner
        | None, false ->
          (* Case 2: top-level sequential — emit [int main()] directly.
             Replace [Tvoid] return type with [int] and every [Sreturn None]
             with [Sreturn (Some (CPPint 0))]. *)
          let int_ty = Tid_external ("int", []) in
          let rec void_return_to_zero = function
            | Sreturn None -> Sreturn (Some (CPPint 0))
            | Sif (c, t, e) ->
              Sif (c, List.map void_return_to_zero t,
                      List.map void_return_to_zero e)
            | Sblock ss -> Sblock (List.map void_return_to_zero ss)
            | Smatch (scrut, branches, default) ->
              Smatch
                ( scrut,
                  List.map
                    (fun br ->
                      { br with smb_body = List.map void_return_to_zero br.smb_body })
                    branches,
                  Option.map (List.map void_return_to_zero) default )
            | s -> s
          in
          ( match inner with
          | Dfun ({df_shape = Ddef (params, body); _} as f) ->
            Dfun
              { f with
                df_ret = int_ty;
                df_shape = Ddef (params, List.map void_return_to_zero body) }
          | d -> d )
        | None, true ->
          (* Case 3: top-level reified — rename to [_main], register for
             wrapper that calls [_main()->run()] *)
          let new_label = Label.of_id (Id.of_string "_main") in
          let new_n = GlobRef.ConstRef (Constant.make2 (Constant.modpath c) new_label) in
          Table.set_main_function (Id.of_string "_main") (ml_codomain ty) None needs_run;
          ( match inner with
          | Dfun f -> Dfun {f with df_path = dfun_path (new_n, [])}
          | d -> d )
      end else
        inner
    | _ -> inner
  in
    (temps, inner, env)
  in
  (* The signature relaxations: each answers one way a template parameter can
     be left with no value at the call site, and each is a no-op on a
     signature that does not have that shape. *)
  let temps, inner =
    List.fold_left
      (fun (temps, inner) relax -> relax temps inner)
      (temps, inner)
      [ relax_applied_return;
        relax_tt_applied_return;
        relax_applied_param;
        deapply_plain_tvars ]
  in
  let temps, inner = default_unmentioned_temps temps inner in
  match temps with
  | [] -> (inner, env)
  | l -> (Dtemplate (l, None, inner), env)

let gen_sfun n b dom cod temps =
  let all_params, b = collect_lams b in
  let n_params = List.length all_params in
  let owned_flags = infer_owned_flags n_params b all_params in
  let ids, env =
    push_vars'
      (List.map
         (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty))
         all_params )
      (empty_env ())
  in
  (* Zip with ownership flags, then filter out void params *)
  let ids_with_owned =
    List.map2 (fun (x, ty) owned -> (x, ty, owned)) ids owned_flags
  in
  let ids_with_owned =
    List.filter (fun (_, ty, _) -> not (ml_type_is_void ty)) ids_with_owned
  in
  (* Convert ML types to C++ types and wrap with const. Owned shared_ptr params:
     pass by value; Borrowed: const ref *)
  let ids =
    List.map
      (fun (x, ty, owned) ->
        let cpp_ty = convert_ml_type_to_cpp_type env [] ty in
        (* Reify monadic parameter types: itree E R → shared_ptr<ITree<R>> *)
        let cpp_ty = reify_monadic_param_type ty cpp_ty in
        let wrapped = wrap_param_by_ownership ~is_owned:owned cpp_ty in
        (Some x, wrapped) )
      ids_with_owned
  in
  let dom = List.filter (fun ty -> ty != Tvoid) dom in
  (* For already-converted C++ types in dom, wrap shared_ptr with const ref *)
  let args =
    List.mapi
      (fun _i ty ->
        let wrapped = wrap_param_by_ownership ty in
        (None, wrapped) )
      dom
  in
  (* Merge parameter names from [ids] (body lambdas) with resolved types
     from [dom] (function signature).  [ids] carries the correct parameter
     names but may have unresolved promoted type vars (e.g. bare [m_carrier]
     instead of [typename _tcI0::m_carrier]).  [dom] carries fully-resolved
     types from the outer gen_dfun but lacks parameter names.  When lengths
     match, zip names from [ids] with types from [args] to get both. *)
  let params =
    if List.length args = List.length ids then
      List.map2
        (fun (name, _) (_, ty) -> (name, ty))
        ids args
    else if List.length args > List.length ids then
      List.rev args
    else
      ids
  in
  let inner = Dfun (mk_dfun n ~ret:cod (Ddecl params)) in
  match temps with
  | [] -> (inner, env)
  | l -> (Dtemplate (l, None, inner), env)

(** Whether a recovered type names an associated type of the enclosing class,
    and so is worth writing back into the binder it came from.  Anything else
    in a body already has a pass that reads it from somewhere better than the
    declaration -- an alias, for one, is a type in its own right and the body
    wants the type it stands for. *)
let rec names_promoted_type_var = function
  | Miniml.Tglob (r, args, _) ->
    Table.is_promoted_type_var r || List.exists names_promoted_type_var args
  | Miniml.Tarr (a, b) -> names_promoted_type_var a || names_promoted_type_var b
  | Miniml.Tmeta {contents = Some t} -> names_promoted_type_var t
  | _ -> false

(** Whether a recovered type says something that means the same at the hole as
    it did in the declaration.

    The gate above asks whether the {e offer} names a promoted type var, which
    is too narrow: the population it misses is the one where the declaration
    knows a perfectly ordinary type.  [memS_mon::bind] declares its
    continuation [std::function<MemS<..,_A1>(_A0)>] and the call is
    [bind<unit, unit>], so the answer [unit] is spelled one line above the
    binder -- and [unit] names no promoted type var.

    A type with no variable in it is one this pass can only get right.  It
    mentions nothing whose meaning depends on where it is read, so it means
    the same at the binder as it did in the declaration.  A variable does not:
    [itreeF]'s [Vis] quantifies over the event's result as well as the tree's,
    and a call that instantiates that existential at the caller's own third
    variable offers a name which, read at the lambda, denotes the deduced type
    of a function parameter.  That offer is faithful to the term and still
    unusable, so variables stay out.

    [Tdummy] is out for the same reason read the other way round: an erased
    position says nothing anywhere, so an offer carrying one cannot beat the
    guess at the same hole -- it only respells [List<T3>] as [List<std::any>].
    Closed is the wrong word for it; the predicate wants types that are both
    closed and informative, and [Tdummy] is the canonical uninformative one. *)
let rec is_closed_type = function
  | Miniml.Tglob (_, args, _) -> List.for_all is_closed_type args
  | Miniml.Tarr (a, b) -> is_closed_type a && is_closed_type b
  | Miniml.Tmeta {contents = Some t} -> is_closed_type t
  | Miniml.Tstring -> true
  | Miniml.Tdummy _ | Miniml.Tvar _ | Miniml.Tapp _
  | Miniml.Tmeta {contents = None} | Miniml.Tunknown | Miniml.Taxiom ->
    false

let writable_offer ty = names_promoted_type_var ty || is_closed_type ty

(** Fill a body's empty type annotations from the declaration, in two passes.

    The first pass is the narrow one and the second widens it: a hole the
    declaration names perfectly well -- but which happens not to mention a
    promoted type var -- would otherwise be declined by the one pass that
    knows the answer.

    A hole neither pass can name is left a hole.  There used to be a third
    pass here that filled every remaining one with the enclosing class's
    first-declared associated type, which is right only when the class
    declares exactly one and the hole is the carrier; where it is not, the
    guess is what the body is printed from, and it pre-empts the passes in
    {!Translation} that can still read the answer off the term. *)
let recover_erased_body_types ty b =
  let b = Mlutil.recover_erased_types ~only:names_promoted_type_var ty b in
  Mlutil.recover_erased_types ~only:writable_offer ~refine_only:true ty b

(** Generate C++ declaration from ML definition (main entry point) *)
let gen_decl__inner n b ty =
  with_body_resolutions n b @@ fun () ->
  with_itree_mode_for ty @@ fun () ->
  with_method_ns_for_locals @@ fun () ->
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
    | Tfun _ ->
      let f, env = gen_dfun n b cty ty temps in
      (f, env, tvars)
    | _ ->
    match b with
    | _ when only_throws b ->
      (* A body that only throws becomes a zero-arg function, so the throw
         happens when the value is asked for rather than during static
         initialisation (which terminates the program before main). *)
      let body_expr = gen_expr (empty_env ()) b in
      let inner = Dfun (mk_dfun n ~ret:cty (Ddef ([], [Sreturn (Some body_expr)]))) in
      ( match temps with
      | [] -> (inner, empty_env (), tvars)
      | l -> (Dtemplate (l, None, inner), empty_env (), tvars) )
    | _ ->
      begin_body ();
      let body_expr =
        with_cpp_return_type (Some cty) (fun () -> gen_expr (empty_env ()) b)
      in
      (* When a unit-typed constant's body calls a void-ified function,
         the call produces no value.  Wrap in an IIFE that executes the
         body for side effects and returns Unit::e_TT. *)
      let body_expr =
        if is_cpp_unit_type cty then
          match body_expr with
          | CPPenum_val _ -> body_expr  (* already a literal *)
          | CPPglob (_, _, Some ci) when ci.ci_inline <> None ->
            body_expr  (* inline custom literal (e.g. std::monostate{}) *)
          | _ ->
            mk_iife None [Sexpr body_expr; Sreturn (Some (mk_tt_expr ()))]
        else body_expr
      in
      let body_expr =
        if resolves_to_any_type cty then erase_fn_for_any_slot b body_expr
        else body_expr
      in
      let inner = snd (deapply_plain_tvars temps (Dasgn (n, cty, body_expr))) in
      ( match temps with
      | [] -> (inner, empty_env (), tvars)
      | l -> (Dtemplate (l, None, inner), empty_env (), tvars) )

let gen_decl n b ty =
  Table.with_decl_ref n (fun () -> gen_decl__inner n b ty)

(** What a top-level function is generated under: its body with erased types
    recovered and type variables resolved against its ML type, its C++ type,
    its template head, and the template parameters callers must see. *)
type function_head = {
  fh_body : ml_ast;
  fh_cty : cpp_type;
  fh_temps : (template_type * Id.t) list;
  fh_tvars : Id.t list;
      (** Typeclass-typed parameters first -- they become template parameters
          inside {!gen_dfun} without appearing in the C++ type, and a caller
          must see them to use the full template definition -- then the C++
          type's variables and the index variables it does not mention. *)
}

(** [with_function_head n b ty k] establishes the scope a top-level function
    [n] is generated in and hands [k] its {!function_head}. *)
let with_function_head n b ty k =
  with_body_resolutions n b @@ fun () ->
  let ty = type_simpl ty in
  let b = recover_erased_body_types ty b in
  let b = resolve_body_tvars b ty in
  with_method_ns_for_locals @@ fun () ->
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars cty in
  let index_tvar_set = collect_ml_type_index_tvars ty in
  let extra_index_tvars =
    IntSet.fold (fun i acc ->
      let id = tvar_id i in
      if List.exists (Id.equal id) tvars then acc
      else id :: acc
    ) index_tvar_set []
    |> List.rev
  in
  let tvars = tvars @ extra_index_tvars in
  let temps =
    phantom_aware_temps ~force_required:index_tvar_set
      ~also_declared:(Ml_type_util.collect_ml_tvars ty) ~ml_ty:ty cty tvars
  in
  let tc_param_ids =
    match ty with
    | Tarr _ -> collect_typeclass_param_ids ty
    | _ -> []
  in
  k ty {fh_body = b; fh_cty = cty; fh_temps = temps; fh_tvars = tc_param_ids @ tvars}

(** [gen_function n ty h] generates the function [n] under [h]: its
    definition, the environment its names were allocated in, and the template
    parameters callers see -- [h]'s, then one per callable parameter. *)
let gen_function n ty h =
  let f, env = gen_dfun n h.fh_body h.fh_cty ty h.fh_temps in
  let callable_tparams =
    match h.fh_cty with
    | Tfun (dom, _) ->
      List.filter_map
        (fun (ty, i) ->
          match ty with
          | Tfun _ when not (Ml_type_util.is_fully_erased_fun_ty ty) ->
            Some (fun_tparam_id i)
          | _ -> None )
        (List.mapi (fun i ty -> (ty, i)) dom)
    | _ -> []
  in
  (f, env, h.fh_tvars @ callable_tparams)

(** Generate C++ declaration with pretty-printing adjustments: a function, a
    constant whose body only throws (as a zero-argument function, so it
    throws when called and not at static initialisation), or [None] for any
    other constant. *)
let gen_decl_for_pp__inner n b ty =
  with_function_head n b ty @@ fun ty h ->
  match h.fh_cty with
  | Tfun _ ->
    let f, env, tvars = gen_function n ty h in
    (Some f, env, tvars)
  | cty when only_throws h.fh_body ->
    let body_expr = gen_expr (empty_env ()) h.fh_body in
    let inner = Dfun (mk_dfun n ~ret:cty (Ddef ([], [Sreturn (Some body_expr)]))) in
    let ds =
      match h.fh_temps with
      | [] -> inner
      | l -> Dtemplate (l, None, inner)
    in
    (Some ds, empty_env (), h.fh_tvars)
  | _ -> (None, empty_env (), h.fh_tvars)

let gen_decl_for_pp n b ty =
  Table.with_decl_ref n (fun () -> gen_decl_for_pp__inner n b ty)

(** Generate a full C++ function definition for a [Dfix] member.  Returns
    [(decl, env, tvars)]. *)
let gen_dfun_def__inner n b ty = with_function_head n b ty (gen_function n)

let gen_dfun_def n b ty =
  Table.with_decl_ref n (fun () -> gen_dfun_def__inner n b ty)

(** Generate C++ function specification (for header files) *)
let gen_spec__inner n b ty =
  with_body_resolutions n b @@ fun () ->
  let ty = type_simpl ty in
  let ml_ty = ty in  (* preserve ML type before C++ conversion *)
  let unit_void = ml_type_is_void_call ty in
  with_method_ns_for_locals @@ fun () ->
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  let result =
    match ty with
    | Tfun (dom, cod) ->
      let cod = apply_unit_void unit_void cod in
      gen_sfun n b dom cod temps
    | _ ->
    match b with
    | _ when only_throws b ->
      (* Throws when called, so: a zero-arg function declaration. *)
      let inner = Dfun (mk_dfun n ~ret:ty (Ddef ([], []))) in
      ( match temps with
      | [] -> (inner, empty_env ())
      | l -> (Dtemplate (l, None, inner), empty_env ()) )
    | _ ->
      (* Expose the constant's C++ type so that inner call sites can recover
         erased template type args (see try_recover_erased_return_type). Without
         this, calls like pick<natBoxed>() inside a constant body cannot deduce
         the missing type parameter. *)
      with_cpp_return_type (Some ty) @@ fun () ->
      (* Strip MLmagic wrapper and track whether a type coercion from std::any
         is needed.  MLmagic wraps expressions when the extraction detects a
         type mismatch (e.g. Obj = std::any vs nat = unsigned int). *)
      let has_magic, inner_body =
        match b with
        | MLmagic (_, inner) -> (true, inner)
        | _ -> (false, b)
      in
      (* The optimization pass (simpl) transforms MLmagic(MLapp(f, args)) into
         MLapp(MLmagic(f), args), pushing the magic inside the application head.
         Detect this so we still insert std::any_cast for the result. *)
      let has_magic =
        has_magic || ml_head_has_magic b
      in
      (* A constant typed by a name -- an instance of a single-method class is
         typed by the class -- may be initialised with a partially applied
         body: [Instance Convert_holder : Convert hbox := fun n => tfmap f],
         where [Convert] stands for two arrows and the body writes one.  The
         slot it initialises is a [std::function] of the full signature, which
         no partial application can fill, so the arrows the name stands for are
         the arrows the body must have. *)
      let inner_body =
        Ml_type_util.eta_expand_to
          (Ml_type_util.expand_ml_fun_alias ml_ty)
          inner_body
      in
      begin_body ();
      (* The constant's own type is also the expected type of its body, so an
         IIFE standing in for a let-in tail expression re-bases onto it rather
         than onto nothing. *)
      let b_expr = gen_expr ~expected_ty:ty (empty_env ()) inner_body in
      (* Wrap with std::any_cast when the C++ expression returns std::any but the
         declared type is concrete.  Two detection paths:
         (a) MLmagic — the extraction explicitly flagged a type coercion.
         (b) Record field projection — the field's return type is a promoted
             type var (erased to std::any) but Coq's type system sees the
             concrete type, so no MLmagic is generated. *)
      let is_concrete_target =
        match ty with
        | Tany | Tvar _ | Tunresolved | Tvoid | Tauto -> false
        | Tglob (g, _, _) when Table.is_erased_type_const g -> false
        | _ -> not (type_is_erased ty)
      in
      let needs_any_cast =
        is_concrete_target
        && (has_magic || ml_body_returns_erased_field inner_body)
      in
      let b_expr =
        if needs_any_cast then unbox_value ty b_expr
        else
          (* (c) The emitted expression is itself the evidence: a projection
             out of a pair that was recovered from a box hands back a
             [std::any] whatever its ML type says, and neither (a) nor (b)
             sees that. *)
          recover_boxed_component ty b_expr
      in
      (* When a unit-typed constant's body may call a void-ified function,
         wrap in an IIFE that executes the body for side effects and
         returns Unit::e_TT.  Pure enum literals need no wrapping. *)
      let b_expr =
        if is_cpp_unit_type ty && ml_type_is_unit ml_ty then
          match b_expr with
          | CPPenum_val _ -> b_expr
          | CPPglob (_, _, Some ci) when ci.ci_inline <> None -> b_expr
          | _ ->
            mk_iife None [Sexpr b_expr; Sreturn (Some (mk_tt_expr ()))]
        else b_expr
      in
      let b_expr =
        if resolves_to_any_type ty then erase_fn_for_any_slot inner_body b_expr
        else b_expr
      in
      (* A type naming a class field this scope cannot resolve would spell
         the field's file-scope erased alias, while the initialiser -- built
         through the instance the term names -- has the real type: [run :=
         @int_to_ptr natIPtr (@PIV natIPtr) ...] is an [EOU<pair<Nat, bool>>],
         not an [EOU<crane::obj>].  The initialiser says it. *)
      let ty = if mentions_unresolved_promoted ty then Tauto else ty in
      (* A polymorphic constant's family parameter is plain, as a
         function's is, and written applied until deapplied. *)
      let inner = snd (deapply_plain_tvars temps (Dasgn (n, Tconst ty, b_expr))) in
      ( match temps with
      | [] -> (inner, empty_env ())
      | l -> (Dtemplate (l, None, inner), empty_env ()) )
  in
  result

let gen_spec n b ty =
  Table.with_decl_ref n (fun () -> gen_spec__inner n b ty)

(** Where a function's definition is written: a template's in the header,
    anything else's in the implementation file. *)
type definition_file = Header | Implementation

type generated_entity =
  | Defined of cpp_decl * definition_file
  | Declared of cpp_decl

type generated_fun = {
  gf_entity : generated_entity;
  gf_env : env;
  gf_lifted : cpp_decl list;
}

let definition_file_of tvars = if tvars = [] then Implementation else Header

let defined d tvars = Defined (d, definition_file_of tvars)

(** Generate each function of a mutually recursive group, translating each
    body once. *)
let gen_dfuns_dual fds =
  List.map
    (fun {fd_ref; fd_body; fd_type} ->
      let (ds, env, tvars), lifted =
        collecting_lifted (fun () -> gen_dfun_def fd_ref fd_body fd_type)
      in
      {gf_entity = defined ds tvars; gf_env = env; gf_lifted = lifted} )
    fds

(** Generate a single Dterm function, translating its body once. *)
let gen_decl_for_pp_dual__inner n b ty =
  let (gf_entity, gf_env), gf_lifted =
    collecting_lifted @@ fun () ->
    match gen_decl_for_pp n b ty with
    | Some ds, env, tvars -> (defined ds tvars, env)
    | None, _, _ ->
      (* Not a function: a declaration, and no definition anywhere. *)
      let spec, env = gen_spec n b ty in
      (Declared spec, env)
  in
  {gf_entity; gf_env; gf_lifted}

let gen_decl_for_pp_dual n b ty =
  Table.with_decl_ref n (fun () -> gen_decl_for_pp_dual__inner n b ty)
