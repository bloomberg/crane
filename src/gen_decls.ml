(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Declaration-level C++ code generation: inductives, records, typeclasses,
    instances, and top-level function definitions. Depends on the
    expression-level codegen in {!Translation}. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Str
open Util
open Translation_state
open Ml_type_util
open Translation

module IntSet = Escape.IntSet

let gen_ind_cpp ?(consarg_names = [||]) vars name cnames tys =
  let constrdecl =
    Array.to_list
      (Array.mapi
         (fun i tys ->
           let c = cnames.(i) in
           let ctor_struct_name = ctor_struct_name_of_ref ~fallback_idx:i c in
           let ctor_consarg_names =
             if i < Array.length consarg_names then consarg_names.(i)
             else []
           in
           let n_fields = List.length tys in
           let field_ids =
             compute_and_register_field_names ctor_struct_name
               (augment_with_args_renaming c ctor_consarg_names)
               ctor_consarg_names n_fields
           in
           let constr =
             List.mapi
               (fun i x ->
                 ( List.nth field_ids i,
                   convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name) vars x ) )
               tys
           in
           let make_args =
             List.map
               (fun (x, _) -> mk_cppglob_local (GlobRef.VarRef x) [])
               constr
           in
           let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
           let make =
             Dfundef
               ( [(c, []); (GlobRef.VarRef (Id.of_string "make"), [])],
                 Tshared_ptr (Tglob (name, ty_vars, [])),
                 List.rev constr,
                 [
                   Sreturn
                     (Some
                        (CPPfun_call
                           ( CPPmk_shared (Tglob (name, ty_vars, [])),
                             [CPPstruct (c, ty_vars, make_args)] ) ) );
                 ],
                 false )
           in
           (ty_vars == [], make) )
         tys )
    |> List.filter_map (fun (keep, make) -> if keep then Some make else None)
  in
  Dnspace (Some name, constrdecl)

(* =========================================================================
   Shared helpers for record and typeclass generation
   ========================================================================= *)

(** Count the actual (non-promoted) type parameters in [ip_sign].  Entries
    marked [Keep] correspond to real template parameters; the remaining
    entries are promoted Type-valued fields. *)
let count_keep_params sign =
  List.length (List.filter (fun x -> x == Keep) sign)

(** Filter [Tdummy] entries from the first constructor's type list.  Both
    [gen_record_cpp] and [gen_typeclass_cpp] need the non-erased types only,
    because [select_fields] already drops the corresponding field names. *)
let non_dummy_constructor_types ind =
  filter_value_types ind.ip_types.(0)

(** Generate C++ struct for a record type.

    Only actual type parameters ([Keep] in [ip_sign]) become C++ template
    parameters.  Promoted Type-valued fields (present in [ip_vars] but past
    the [Keep] entries) are erased to [std::any] — they have no C++ template
    counterpart in a plain struct (unlike typeclasses, which turn them into
    [typename I::field] requirements). *)
let gen_record_cpp name fields ind =
  let nb_keep = count_keep_params ind.ip_sign in
  let param_ip_vars = List.filteri (fun i _ -> i < nb_keep) ind.ip_vars in
  let vars = List.map Common.tparam_name param_ip_vars in
  (* Use full ip_vars for type name resolution so Tvars resolve to names,
     then replace promoted Tvars (not in template params) with std::any. *)
  let all_vars = List.map Common.tparam_name ind.ip_vars in
  let promoted_var_names =
    List.filteri (fun i _ -> i >= nb_keep) ind.ip_vars
    |> List.map (fun id -> Id.to_string (Common.tparam_name id))
  in
  let replace_promoted = function
    | Tvar (_, Some id) when List.mem (Id.to_string id) promoted_var_names ->
      Tany
    | Tglob (g, _, _) when Table.is_promoted_type_var g ->
      ( match Table.promoted_type_var_name g with
      | Some var_id when List.mem (Id.to_string var_id) promoted_var_names ->
        Tany
      | _ -> Tany )
    | ty -> ty
  in
  let l = List.combine fields (non_dummy_constructor_types ind) in
  let l =
    List.mapi
      (fun i (x, t) ->
        let n =
          match x with
          | Some n -> n
          | None -> GlobRef.VarRef (Id.of_string ("_field" ^ string_of_int i))
        in
        let ct =
          convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
            all_vars
            t
        in
        let ct = Minicpp.map_cpp_type replace_promoted ct in
        ( Fvar' (n, ct), VPublic, SNoTag ) )
      l
  in
  let ty_vars = List.map (fun x -> (TTtypename, x)) vars in
  Dstruct
    {
      ds_ref = name;
      ds_fields = l;
      ds_tparams = ty_vars;
      ds_constraint = None;
      ds_needs_shared_from_this = false;
    }

(** Generate a C++ concept from a type class.
   Type class Eq(A) with method eqb : A -> A -> bool becomes:
   template<typename I, typename A>
   concept Eq = requires(A a0, A a1) {
     { I::eqb(a0, a1) } -> std::convertible_to<bool>;
   };

   Uses CPPconvertible_to with the actual cpp_type for the constraint,
   which will be pretty-printed in cpp.ml.
*)
let gen_typeclass_cpp name fields ind =
  let nb_keep = count_keep_params ind.ip_sign in
  let inst_id =
    let param_names =
      List.mapi (fun i x -> if i < nb_keep
                            then Id.to_string (Common.tparam_name x)
                            else "") ind.ip_vars
    in
    if List.mem "I" param_names then Id.of_string "_Inst"
    else Id.of_string "I"
  in
  (* Split ip_vars into param vars (real type params) and promoted vars
     (associated types). Prefix param vars with t_ for BDE convention. *)
  let prefixed_ip_vars =
    List.mapi
      (fun i x -> if i < nb_keep then Common.tparam_name x else x)
      ind.ip_vars
  in
  let param_vars = List.filteri (fun i _ -> i < nb_keep) prefixed_ip_vars in
  let promoted_vars =
    List.filteri (fun i _ -> i >= nb_keep) prefixed_ip_vars
  in
  (* Only param vars become concept template parameters; promoted vars become
     typename requirements inside the requires block *)
  let ty_vars = List.map (fun x -> (TTtypename, x)) param_vars in
  let all_params = (TTtypename, inst_id) :: ty_vars in
  (* Build typename requirements for promoted vars: typename I::field; *)
  let type_reqs =
    List.map
      (fun var_id -> Tqualified (Tvar (0, Some inst_id), var_id))
      promoted_vars
  in
  let non_dummy_types = non_dummy_constructor_types ind in
  let method_list =
    ( try List.combine fields non_dummy_types
      with _ ->
        List.map (fun f -> (f, Miniml.Tunknown)) fields )
  in
  (* Build a mapping for promoted vars from nested typeclasses.

     When a promoted field has typeclass type (e.g., [base_category :
     PreCategory]), the nested typeclass's own promoted vars (e.g., [Obj])
     may appear in other fields' types (e.g., [zero_object : Obj
     base_category]).  During extraction, these become [Tvar(1000, Some
     "Obj")] — indistinguishable from a direct promoted var of the current
     typeclass.

     We build a mapping [Obj → typename I::base_category::Obj] so that
     [subst_promoted_in_cpp_type] can resolve them correctly through the
     promoted field rather than leaving a dangling bare [Obj]. *)
  let nested_promoted_map =
    List.concat_map
      (fun (field_opt, field_ty) ->
        match (field_opt, field_ty) with
        | Some _field_ref, Miniml.Tglob (r, _, _) when Table.is_typeclass r ->
          let field_name_str = Common.pp_global_name Term _field_ref in
          let field_id = Id.of_string field_name_str in
          if List.exists (Id.equal field_id) promoted_vars then
            let nested_ip_vars = Table.get_ind_ip_vars r in
            let nested_nb_keeps = Table.get_ind_nb_sign_keeps r in
            let nested_promoted =
              List.filteri (fun i _ -> i >= nested_nb_keeps) nested_ip_vars
            in
            List.map
              (fun nested_var ->
                ( nested_var,
                  Tqualified
                    (Tqualified (Tvar (0, Some inst_id), field_id), nested_var)
                ) )
              nested_promoted
          else
            []
        | _ -> [] )
      method_list
  in
  (* Substitute promoted Tvars with [Tqualified(I, name)] in cpp_type trees.
     After conversion, promoted vars appear as [Tvar(_, Some name)] where
     name is in [promoted_vars].  Replace with [typename I::name].
     Also handles nested promoted vars from typeclass-typed promoted fields
     via [nested_promoted_map] — e.g., [Obj] from [PreCategory] becomes
     [typename I::base_category::Obj] when [base_category] is a promoted
     [PreCategory]-typed field. *)
  let rec subst_promoted_in_cpp_type = function
    | Tvar (_, Some vname) when List.exists (Id.equal vname) promoted_vars ->
      Tqualified (Tvar (0, Some inst_id), vname)
    | Tvar (_, Some vname) -> (
      match
        List.find_opt (fun (n, _) -> Id.equal n vname) nested_promoted_map
      with
      | Some (_, replacement) -> replacement
      | None -> Tvar (0, Some vname) )
    | Tfun (args, ret) ->
      Tfun
        ( List.map subst_promoted_in_cpp_type args,
          subst_promoted_in_cpp_type ret )
    | Tglob (r, ts, es) -> Tglob (r, List.map subst_promoted_in_cpp_type ts, es)
    | Tshared_ptr t -> Tshared_ptr (subst_promoted_in_cpp_type t)
    | Tnamespace (r, t) -> Tnamespace (r, subst_promoted_in_cpp_type t)
    | Tqualified (b, id) -> Tqualified (subst_promoted_in_cpp_type b, id)
    | Tref t -> Tref (subst_promoted_in_cpp_type t)
    | Tvariant ts -> Tvariant (List.map subst_promoted_in_cpp_type ts)
    | Tid (id, ts) -> Tid (id, List.map subst_promoted_in_cpp_type ts)
    | Tid_external (id, ts) -> Tid_external (id, List.map subst_promoted_in_cpp_type ts)
    | Tmod (m, t) -> Tmod (m, subst_promoted_in_cpp_type t)
    | t -> t
  in
  (* Check if a type is a bare promoted Tvar — a Tvar whose index is beyond the
     real type parameters. This indicates the field's type is entirely
     determined by a promoted associated type, so we can't decompose it into
     args and return type at concept time (the concrete type might be a
     function). *)
  let is_bare_promoted_tvar ty =
    match ty with
    | Miniml.Tvar n -> n > nb_keep
    | _ -> false
  in
  (* Check if a field type is a typeclass-typed promoted field.  Such
     fields become [typename I::field] requirements (already in type_reqs)
     and should NOT generate method requirements in the concept body. *)
  let is_typeclass_field_type ty =
    match ty with
    | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
    | _ -> false
  in
  (* Generate a single method requirement. Returns either: - `Normal (params,
     (call, constraint))` for regular methods - `Disjunctive expr` for fields
     whose type is a bare promoted Tvar *)
  let gen_method_req (field_opt, field_ty) =
    match field_opt with
    | None -> None (* Anonymous field, skip *)
    | Some field_ref ->
      let method_name = Common.pp_global_name Term field_ref in
      if is_typeclass_field_type field_ty then
        (* TypeClass-typed field — skip method requirement.  The field
           is promoted and already has a [typename I::field;] type
           requirement in [type_reqs].  Adding a method requirement
           would try to use the concept name as a concrete type
           (e.g., [std::shared_ptr<PreCategory>]) which is invalid. *)
        None
      else if is_bare_promoted_tvar field_ty then
        (* Field type is a bare promoted Tvar (e.g., fun_ind_prf :
           fun_ind_prf_ty). The concrete type could be a plain value or a
           function with any arity. Generate a disjunctive concept requirement:
           requires { { I::method() } -> std::convertible_to<T>; } || requires {
           { I::method } -> std::convertible_to<T>; } The first clause handles
           nullary accessors (Meyers singleton pattern). The second handles
           functions (pointer converts to std::function) and static data members
           (direct value). *)
        let ret_cpp =
          convert_ml_type_to_cpp_type
            (empty_env ())
            prefixed_ip_vars
            field_ty
        in
        let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
        let constraint_expr = CPPconvertible_to ret_cpp in
        let qualified =
          CPPqualified (CPPvar inst_id, Id.of_string method_name)
        in
        let call_form =
          CPPrequires ([], [(CPPfun_call (qualified, []), constraint_expr)], [])
        in
        let value_form = CPPrequires ([], [(qualified, constraint_expr)], []) in
        Some (`Disjunctive (CPPbinop ("||", call_form, value_form)))
      else
        let args, ret = get_args_and_ret [] field_ty in
        (* Filter out type class instance arguments (they're passed via
           template) *)
        let args =
          List.filter (fun t ->
            not (Table.is_typeclass_type t) && not (Mlutil.isTdummy t)) args
        in
        let ret_cpp =
          convert_ml_type_to_cpp_type
            (empty_env ())
            prefixed_ip_vars
            ret
        in
        let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
        (* Emit each argument inline as [std::declval<ArgType>()] rather than
           binding it to a shared [requires(...)] parameter.  A requires-
           expression has a single parameter list shared across all its
           requirement lines, so naming arguments positionally (a0, a1, ...)
           and deduplicating by name aliases parameters of different types
           across methods (e.g. [g : T -> T] would reuse [a0 : pair<T,T>]
           left over from [f : T*T -> T]).  Using [declval] gives each method
           its own correctly-typed arguments, matching the module-type concept
           idiom in [cpp.ml]'s [pp_spec_as_requirement]. *)
        let arg_declvals =
          List.map
            (fun arg_ty ->
              let arg_cpp =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  prefixed_ip_vars
                  arg_ty
              in
              CPPdeclval (subst_promoted_in_cpp_type arg_cpp) )
            args
        in
        (* Method call: I::method_name(std::declval<...>(), ...).
           CPPfun_call stores args reversed (the printer applies List.rev
           when rendering), so we pre-reverse to get the correct printed
           order. *)
        let call_args = List.rev arg_declvals in
        let call =
          CPPfun_call
            (CPPqualified (CPPvar inst_id, Id.of_string method_name), call_args)
        in
        (* Constraint: use the cpp_type directly - cpp.ml will render it *)
        let constraint_expr = CPPconvertible_to ret_cpp in
        Some (`Normal ([], (call, constraint_expr)))
  in
  let all_reqs =
    List.filter_map (fun pair -> gen_method_req pair) method_list
  in
  (* Separate normal requirements from disjunctive ones *)
  let normal_reqs =
    List.filter_map
      (function
        | `Normal r -> Some r
        | _ -> None )
      all_reqs
  in
  let disjunctive_exprs =
    List.filter_map
      (function
        | `Disjunctive e -> Some e
        | _ -> None )
      all_reqs
  in
  (* Build the concept body. Normal requirements go in a single requires{}
     block. Disjunctive requirements (for bare-Tvar fields) are &&-ed
     separately, each wrapped in parentheses via the || rendering. *)
  let concept_body =
    let normal_part =
      if normal_reqs = [] then
        None
      else
        (* Arguments are emitted inline as [std::declval<...>()], so the
           requires-expression needs no parameter list. *)
        let constraints = List.map snd normal_reqs in
        Some (CPPrequires ([], constraints, type_reqs))
    in
    match (normal_part, disjunctive_exprs) with
    | Some np, [] -> np
    | None, [d] ->
      if type_reqs <> [] then
        CPPbinop ("&&", CPPrequires ([], [], type_reqs), d)
      else
        d
    | None, d :: rest ->
      let base =
        if type_reqs <> [] then
          CPPbinop ("&&", CPPrequires ([], [], type_reqs), d)
        else
          d
      in
      List.fold_left (fun acc e -> CPPbinop ("&&", acc, e)) base rest
    | Some np, ds -> List.fold_left (fun acc e -> CPPbinop ("&&", acc, e)) np ds
    | None, [] ->
      if type_reqs <> [] then
        CPPrequires ([], [], type_reqs)
      else
        CPPrequires ([], [], [])
    (* degenerate: no requirements *)
  in
  Dtemplate (all_params, None, Dconcept (name, concept_body))

(** Generate a C++ struct for a type class instance.
   Type class instances become structs with static methods.
   Example: Instance IntEq : Eq int := { eqb := Int.eqb }.
   becomes: struct IntEq { static bool eqb(int a, int b) { ... } };

   Returns: (struct_decl option, class_ref option, type_args)
   The class_ref and type_args are used to generate static_assert in cpp.ml *)
let gen_instance_struct (name : GlobRef.t) (body : ml_ast) (ty : ml_type) :
    cpp_decl option * GlobRef.t option * ml_type list =
  (* For parameterized instances, strip Tarr/MLlam layers to get to the inner
     typeclass type and constructor body. Collect template parameters along the
     way. Example: numOption has type Tarr(Tdummy, Tarr(Tglob(Numeric,[A],[]),
     Tglob(Numeric,[option A],[]))) and body MLlam(_, Tdummy, MLlam(_,
     Tglob(Numeric,...), MLcons(...))) *)
  let rec strip_outer_layers ty body tc_idx tc_acc lam_acc =
    match (ty, body) with
    | Tarr (arg_ty, rest_ty), MLlam (ml_id, lam_ty, rest_body) ->
      if Mlutil.isTdummy arg_ty then
        (* Erased type parameter — skip (template params are inferred from type
           variables in the return type via collect_ml_tvars below) *)
        strip_outer_layers
          rest_ty
          rest_body
          tc_idx
          tc_acc
          ((id_of_mlid ml_id, lam_ty) :: lam_acc)
      else if Table.is_typeclass_type arg_ty then
        (* Typeclass constraint — becomes a concept-constrained template
           parameter.  E.g., [PreCategory _tcI0] instead of [typename
           _tcI0], so the compiler enforces concept satisfaction. *)
        let instance_name = tc_instance_id tc_idx in
        let tt =
          match arg_ty with
          | Tglob (r, type_args, _) ->
            (* Unary concepts (nb_sign_keeps = 0) are expressed inline as
               [Eq _tcI0].  Multi-parameter concepts like [Numeric<I, t_A>]
               carry their kept type args so a [requires C<_tcI0, T1>] clause
               can be emitted at the use site instead of silently degrading to
               an unconstrained [typename] (CWE-693 / CWE-345). *)
            let nb_keeps = Table.get_ind_nb_sign_keeps r in
            if nb_keeps = 0 then TTconcept (r, [])
            else
              let type_arg_cpp =
                List.map
                  (convert_ml_type_to_cpp_type (empty_env ()) [])
                  type_args
              in
              TTconcept (r, type_arg_cpp)
          | _ -> TTtypename
        in
        strip_outer_layers
          rest_ty
          rest_body
          (tc_idx + 1)
          ((tt, instance_name) :: tc_acc)
          ((instance_name, lam_ty) :: lam_acc)
      else (* Not a type param or typeclass — stop stripping *)
        (ty, body, List.rev tc_acc, List.rev lam_acc)
    | _ -> (ty, body, List.rev tc_acc, List.rev lam_acc)
  in
  let inner_ty, inner_body, tc_temps, lam_params =
    strip_outer_layers ty body 0 [] []
  in
  (* Collect type variables from the inner return type's type args. For
     parameterized instances like numOption : Numeric (option A), the return
     type is Tglob(Numeric, [option A], []) which contains Tvar for A. These
     need to become template typename parameters (T1, T2, etc.). *)
  let rec collect_ml_tvars acc = function
    | Miniml.Tvar i ->
      if List.mem i acc then
        acc
      else
        i :: acc
    | Miniml.Tarr (t1, t2) -> collect_ml_tvars (collect_ml_tvars acc t1) t2
    | Miniml.Tglob (_, tys, _) -> List.fold_left collect_ml_tvars acc tys
    | _ -> acc
  in
  let tv_temps =
    match inner_ty with
    | Tglob (_, type_args, _) ->
      let raw = List.fold_left collect_ml_tvars [] type_args in
      List.sort compare raw
      |> List.mapi (fun i _ -> (TTtypename, tvar_id (i + 1)))
    | _ -> []
  in
  (* Template params: typeclass params first, then type vars (matches gen_dfun
     convention) *)
  let template_params = tc_temps @ tv_temps in
  (* Now inner_ty should be Tglob(class_ref, type_args, _) and inner_body should
     be MLcons(...) *)
  match inner_ty with
  | Tglob (class_ref, type_args, _) when Table.is_typeclass class_ref ->
    (* Get the type class fields (method names) and field types (from
       ind_packet) *)
    let fields = Table.record_fields_of_type inner_ty in
    let field_types =
      List.filter
        (fun t -> not (Mlutil.isTdummy t))
        (Table.record_field_types class_ref)
    in
    (* Strip MLmagic wrapper if present — promoted dependent records may have
       their constructor wrapped in MLmagic due to Tvar/Tglob mismatches during
       extraction unification. *)
    let inner_body =
      match inner_body with
      | MLmagic b -> b
      | b -> b
    in
    ( match inner_body with
    | MLcons (cons_ty, _ctor_ref, method_bodies) ->
      (* For promoted dependent records, the definition type Tglob(Magma,[],[])
         has no type_args, but the MLcons type Tglob(Magma,[nat],[]) carries the
         concrete types extracted from the erased constructor args. *)
      let type_args =
        match cons_ty with
        | Tglob (_, ta, _) when ta <> [] -> ta
        | _ -> type_args
      in
      (* Register promoted type bindings for this instance so that call sites
         (eta_fun) can substitute promoted Tvars with concrete types. E.g., for
         nat_magma : Magma, register [(carrier, nat)] so pick_op<nat_magma>
         eta-expansion uses unsigned int instead of std::any. *)
      let ip_vars = Table.get_ind_ip_vars class_ref in
      let nb_sign_keeps_inst = Table.get_ind_nb_sign_keeps class_ref in
      let promoted_vars =
        List.filteri (fun i _ -> i >= nb_sign_keeps_inst) ip_vars
      in
      let promoted_concrete =
        if List.length type_args > nb_sign_keeps_inst then
          List.filteri (fun i _ -> i >= nb_sign_keeps_inst) type_args
        else
          []
      in
      if
        List.length promoted_vars = List.length promoted_concrete
        && promoted_vars <> []
      then
        Table.add_instance_promoted_types
          name
          (List.map2
             (fun var_name ml_ty -> (var_name, ml_ty))
             promoted_vars
             promoted_concrete );
      (* Build the environment with lambda parameters for de Bruijn resolution.
         For parameterized instances, method bodies reference the outer lambda
         parameters (e.g., the typeclass dictionary) via MLrel indices. We push
         lam_params into the env so these references resolve correctly. *)
      let base_env = snd (push_vars' (List.rev lam_params) (empty_env ())) in
      (* Collect type var names for convert_ml_type_to_cpp_type *)
      let type_var_names = List.map snd tv_temps in
      (* Set up type variable context for fixpoint lifting. Without this,
         fixpoints inside methods get lifted with wrong names and missing
         template parameters. *)
      let saved_outer_name = tctx.current_outer_function_name in
      tctx.current_outer_function_name <- Some (Common.pp_global_name Term name);
      set_current_type_vars type_var_names;
      (* Generate static methods for each field *)
      let gen_method (field_ref, field_ml_ty) field_body =
        match field_ref with
        | None -> None (* Anonymous field, skip *)
        | Some method_ref ->
          (* Skip typeclass-typed fields — they are promoted and handled
             by [using] declarations, not methods.  E.g., [base_category :
             PreCategory] becomes [using base_category = ...;], not a
             static method returning the typeclass. *)
          let is_tc_field =
            match field_ml_ty with
            | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
            | _ -> false
          in
          if is_tc_field then
            None
          else
          let method_name =
            Id.of_string (Common.pp_global_name Term method_ref)
          in
          (* Strip MLmagic wrappers from the field body — promoted dependent
             records produce MLmagic due to Tvar/Tglob mismatches. *)
          let rec strip_magic = function
            | MLmagic b -> strip_magic b
            | b -> b
          in
          let field_body = strip_magic field_body in
          (* Substitute type class parameter with instance's type arg in the
             field type. This gives us the concrete return type (e.g., bool for
             eqb: A -> A -> bool). For promoted dependent records, type_args may
             be empty, leaving Tvars unsubstituted — we handle that below by
             using lambda binder types. *)
          let subst_ty = Mlutil.type_subst_list type_args field_ml_ty in
          (* Extract parameter names and types from the lambda. For promoted
             type vars (e.g., Tvar 3 for edge in Graph), substitute them with
             their concrete types from type_args. Only substitute Tvars beyond
             the ip_sign Keep count to avoid disturbing regular type variable
             references. *)
          let nb_sign_keeps = List.length tv_temps in
          let subst_promoted_tvars ty =
            if List.length type_args > nb_sign_keeps then
              let rec subst = function
                | Miniml.Tvar j
                  when j > nb_sign_keeps && j <= List.length type_args ->
                  List.nth type_args (j - 1)
                | Miniml.Tarr (a, b) -> Miniml.Tarr (subst a, subst b)
                | Miniml.Tglob (r, l, a) -> Miniml.Tglob (r, List.map subst l, a)
                | Miniml.Tmeta {contents = Some t} -> subst t
                | Miniml.Tmeta _ as t -> t
                | t -> t
              in
              subst ty
            else
              ty
          in
          let rec extract_params ml_acc cpp_acc body =
            match body with
            | MLlam (_id, ty, rest) when Mlutil.isTdummy ty ->
              extract_params ml_acc cpp_acc rest
            | MLlam (id, ty, rest) ->
              let param_name = id_of_mlid id in
              let resolved_ty = subst_promoted_tvars ty in
              let param_cpp_ty =
                convert_ml_type_to_cpp_type
                  base_env
                  type_var_names
                  resolved_ty
              in
              extract_params
                ((param_name, resolved_ty) :: ml_acc)
                ((param_name, param_cpp_ty) :: cpp_acc)
                rest
            | _ -> (List.rev ml_acc, List.rev cpp_acc, body)
          in
          let ml_params, cpp_params, inner_body =
            extract_params [] [] field_body
          in
          (* Determine return type: if type_subst resolved everything, use the
             substituted type. Otherwise, infer from the lambda binders. *)
          let method_ret_ty =
            let ret = ml_return_type subst_ty in
            match ret with
            | (Tvar _ | Tvar' _) when ml_params <> [] ->
              (* Unsubstituted Tvar — infer from the last lambda binder's type.
                 For op : A -> A -> A with body MLlam(x, nat, MLlam(y, nat,
                 ...)), the return type is the same as the parameter type
                 (nat). *)
              let last_param_ty = snd (List.hd (List.rev ml_params)) in
              convert_ml_type_to_cpp_type
                base_env
                type_var_names
                last_param_ty
            | Tvar _ | Tvar' _ ->
              (* No lambda binders to infer from — try to use the field type's
                 arg types. For a non-function field like m_id : carrier, the
                 whole type is Tvar, so look at the body's type. *)
              Tany
            | _ ->
              convert_ml_type_to_cpp_type
                base_env
                type_var_names
                ret
          in
          let cpp_params, ret_ty, body_stmts =
            if ml_params = [] then
              (* No lambdas in the body — either a function reference that needs
                 eta-expansion, or a non-function value field. *)
              let all_arg_types, _ret_type = get_args_and_ret [] subst_ty in
              (* Filter out type class instance and erased args *)
              let arg_types =
                List.filter (fun t ->
                  not (Table.is_typeclass_type t) && not (Mlutil.isTdummy t))
                  all_arg_types
              in
              if arg_types = [] then
                (* Non-function field (like m_id : carrier) — generate as a
                   static value with a nullary accessor method. *)
                let stmts =
                  gen_stmts base_env (fun x -> Sreturn (Some x)) inner_body
                in
                ([], method_ret_ty, stmts)
              else
                (* Function reference — eta-expand.  Build C++ params only for
                   real args, but supply MLdummy for erased args in the ML
                   application so the body receives all expected arguments. *)
                let params =
                  List.mapi
                    (fun i arg_ty ->
                      let name = Id.of_string ("a" ^ string_of_int i) in
                      let cpp_ty =
                        convert_ml_type_to_cpp_type
                          base_env
                          type_var_names
                          arg_ty
                      in
                      (name, arg_ty, cpp_ty) )
                    arg_types
                in
                let nparams = List.length params in
                let ml_rels =
                  let real_idx = ref nparams in
                  List.map (fun t ->
                    if Mlutil.isTdummy t || Table.is_typeclass_type t then
                      MLdummy Ktype
                    else begin
                      let r = MLrel !real_idx in
                      decr real_idx; r
                    end
                  ) all_arg_types
                in
                (* Lift the body's de Bruijn indices to account for the new eta
                   params *)
                let lifted_body = Mlutil.ast_lift nparams inner_body in
                let call_expr = MLapp (lifted_body, ml_rels) in
                (* Look up body function's types to detect mismatches from
                   inlined constants (e.g. Ref => "%t0" makes Ref A -> std::any
                   but refToIxNat expects RefNat).  Use the concrete types for
                   the env so method dispatch works, then prepend any_cast
                   bindings for params whose signature type is std::any. *)
                let body_arg_types =
                  match inner_body with
                  | MLglob (r, _) -> (
                    try
                      let bty = Table.find_type r in
                      let bargs, _ = get_args_and_ret [] bty in
                      let bargs = List.filter (fun t ->
                        not (Mlutil.isTdummy t)
                        && not (Table.is_typeclass_type t)) bargs in
                      if List.length bargs = List.length params then
                        Some bargs
                      else None
                    with Not_found -> None )
                  | _ -> None
                in
                let cast_info =
                  List.filter_map (fun (i, (name, ml_ty, _cpp_ty)) ->
                    match body_arg_types with
                    | Some bargs ->
                      let body_ty = List.nth bargs i in
                      let sig_cpp = convert_ml_type_to_cpp_type
                        base_env type_var_names ml_ty in
                      let body_cpp = convert_ml_type_to_cpp_type
                        base_env type_var_names body_ty in
                      if sig_cpp = Tany && body_cpp <> Tany then
                        Some (name, body_ty, body_cpp)
                      else None
                    | None -> None
                  ) (List.mapi (fun i x -> (i, x)) params)
                in
                let ml_vars =
                  List.rev (List.map (fun (name, ml_ty, _cpp_ty) ->
                    match List.find_opt (fun (n, _, _) -> Id.equal n name) cast_info with
                    | Some (_, body_ty, _) -> (name, body_ty)
                    | None -> (name, ml_ty)
                  ) params)
                in
                let renamed_eta, env = push_vars' ml_vars base_env in
                let stmts =
                  gen_stmts env (fun x -> Sreturn (Some x)) call_expr
                in
                let stmts =
                  List.fold_left (fun acc (name, _body_ty, body_cpp) ->
                    let param_name =
                      Id.of_string ("_p_" ^ Id.to_string name) in
                    Sasgn (name, Some body_cpp,
                           CPPany_cast (body_cpp, CPPvar param_name)) :: acc
                  ) stmts (List.rev cast_info)
                in
                (* Sync param names with push_vars' output (lowercased
                   and uniquified) so signatures match bodies.  ml_vars
                   was built via List.rev_map, so renamed_eta is in
                   reversed order — reverse back to align with params. *)
                let cpp_params =
                  List.map2
                    (fun (new_name, _) (_, cpp_ty) ->
                      let needs_cast =
                        List.exists (fun (n, _, _) ->
                          Id.equal n new_name) cast_info in
                      if needs_cast then
                        (Id.of_string ("_p_" ^ Id.to_string new_name), cpp_ty)
                      else
                        (new_name, cpp_ty))
                    (List.rev renamed_eta)
                    (List.map (fun (name, _, cpp_ty) -> (name, cpp_ty)) params)
                in
                (cpp_params, method_ret_ty, stmts)
            else
              (* Normal case: we have lambdas.  push_vars' lowercases
                 and uniquifies names for the de Bruijn environment;
                 sync cpp_params so the method signature matches. *)
              let renamed_ml, env =
                push_vars' (List.rev ml_params) base_env
              in
              let cpp_params =
                List.map2
                  (fun (new_name, _) (_, cpp_ty) -> (new_name, cpp_ty))
                  (List.rev renamed_ml)
                  cpp_params
              in
              let stmts =
                gen_stmts env (fun x -> Sreturn (Some x)) inner_body
              in
              (cpp_params, method_ret_ty, stmts)
          in
          Some
            ( Fmethod
                {
                  mf_name = method_name;
                  mf_tparams = [];
                  mf_ret_type = ret_ty;
                  mf_params = cpp_params;
                  mf_body = body_stmts;
                  mf_is_const = false;
                  mf_is_static = true;
                  mf_is_inline = false;
                  mf_this_pos = 0;
                  mf_no_pure = false;
                  mf_is_noexcept = false;
                },
              VPublic,
              SNoTag )
      in
      (* Zip fields with their types from ind_packet *)
      let fields_with_types =
        if List.length fields = List.length field_types then
          List.combine fields field_types
        else (* Fallback: pair fields with Tunknown if lengths don't match *)
          List.map (fun f -> (f, Miniml.Tunknown)) fields
      in
      let method_pairs = List.combine fields_with_types method_bodies in
      let methods =
        List.filter_map
          (fun ((fld, fty), body) -> gen_method (fld, fty) body)
          method_pairs
      in
      (* Generate [using] declarations for promoted typeclass-typed fields
         from the constructor body.  For such fields, the constructor arg
         is a value expression (e.g., [MLglob nat_category] or
         [MLapp(opposite_category, [MLproj(...)])]) that must be
         translated to a C++ TYPE expression (e.g., [nat_category] or
         [opposite_category<typename _tcI0::base_category>]).

         This function interprets an ML expression at the type level:
         - [MLglob r] → named type [Tglob(r, ...)]
         - [MLapp(MLglob r, args)] → template type with type args
         - [MLrel i] → template parameter reference [Tvar(0, Some name)]
         - [MLmagic e] → strip magic wrapper *)
      let rec ml_expr_to_cpp_type body =
        match body with
        | MLglob (r, _) -> Tglob (r, [], [])
        | MLapp (MLglob (r, _), args) ->
          let type_args = List.filter_map ml_expr_to_cpp_type_opt args in
          Tglob (r, type_args, [])
        | MLapp (f, args) -> (
          match ml_expr_to_cpp_type f with
          | Tglob (r, existing, es) ->
            let type_args = List.filter_map ml_expr_to_cpp_type_opt args in
            Tglob (r, existing @ type_args, es)
          | other -> other )
        | MLrel i -> (
          try
            let name = get_db_name i base_env in
            Tvar (0, Some name)
          with Failure _ -> Tany )
        | MLmagic e -> ml_expr_to_cpp_type e
        | MLcase (_, scrutinee, branches)
          when Array.length branches = 1 ->
          (* Single-branch case = record field projection.  The branch
             destructures the record into named bindings and selects one
             via [MLrel].  Translate into [Tqualified(scrutinee, field)]. *)
          let (binds, _, _, br_body) = branches.(0) in
          let base_ty = ml_expr_to_cpp_type scrutinee in
          ( match br_body with
          | MLrel j when j >= 1 && j <= List.length binds ->
            (* de Bruijn: 1 = last binding, n = first binding *)
            let idx = List.length binds - j in
            let (field_id, _) = List.nth binds idx in
            ( match field_id with
            | Id name | Tmp name -> Tqualified (base_ty, name)
            | Dummy -> Tany )
          | _ ->
            (* Non-trivial body — recurse with extended environment *)
            ml_expr_to_cpp_type br_body )
        | _ -> Tany
      and ml_expr_to_cpp_type_opt body =
        match ml_expr_to_cpp_type body with
        | Tany -> None
        | t -> Some t
      in
      (* Check if an ML expression is a parameterized reference whose
         typeclass arguments have been erased — e.g.,
         [MLapp(MLglob opposite_category, [MLdummy Ktype])].  Such
         references produce incomplete [Tglob(r, [], [])] that can't
         be used as using declarations. *)
      let tc_promoted_usings =
        if List.length fields_with_types = List.length method_bodies then
          List.filter_map
            (fun ((fld, fty), body) ->
              match (fld, fty) with
              | Some field_ref, Miniml.Tglob (r, _, _)
                when Table.is_typeclass r ->
                let has_erased_tc_args =
                  match body with
                  | MLapp (_, args) ->
                    List.exists
                      (function MLdummy _ -> true | _ -> false)
                      args
                  | _ -> false
                in
                if has_erased_tc_args then
                  (* Parameterized reference with erased typeclass args.
                     Fall through to let forwarded_usings handle this
                     field. *)
                  None
                else
                  let field_name_str =
                    Common.pp_global_name Term field_ref
                  in
                  let field_id = Id.of_string field_name_str in
                  let cpp_ty = ml_expr_to_cpp_type body in
                  if cpp_ty = Tany then None
                  else
                    Some
                      ( Fnested_using (field_id, cpp_ty),
                        VPublic,
                        SNoTag )
              | _ -> None )
            (List.combine fields_with_types method_bodies)
        else
          []
      in
      (* Restore type variable context *)
      tctx.current_outer_function_name <- saved_outer_name;
      clear_current_type_vars ();
      (* Compute promoted vars and generate using fields. Promoted vars are
         ip_vars entries beyond the real type parameter count (as determined by
         ip_sign Keep count, not tv_temps which reflects the instance's own type
         variables). They become `using field = ConcreteType;` in the struct. *)
      let ip_vars = Table.get_ind_ip_vars class_ref in
      let nb_sign_keeps_for_promoted = Table.get_ind_nb_sign_keeps class_ref in
      let promoted_vars =
        List.filteri (fun i _ -> i >= nb_sign_keeps_for_promoted) ip_vars
      in
      let promoted_concrete_types =
        if List.length type_args > nb_sign_keeps_for_promoted then
          List.filteri (fun i _ -> i >= nb_sign_keeps_for_promoted) type_args
        else
          []
      in
      (* Is [cpp_ty] a self-referential promoted-var reference (e.g.,
         [Tvar(_, Some "Obj")] where "Obj" is a promoted var)?  Such
         types are useless: [using Obj = Obj;] would just alias the
         enclosing scope, not the template parameter's type. *)
      let is_self_referential_promoted var_name cpp_ty =
        match cpp_ty with
        | Tvar (_, Some id) when Id.equal id var_name -> true
        | _ -> false
      in
      (* For each concept-constrained template parameter, forward its
         promoted type aliases into this struct.  E.g., if [_tcI0]
         satisfies [PreCategory] which has promoted [Obj], generate
         [using Obj = typename _tcI0::Obj;]. *)
      let forwarded_usings =
        List.concat_map
          (fun (tt, tc_name) ->
            match tt with
            | TTconcept (class_ref_tc, _) ->
              let tc_ip_vars = Table.get_ind_ip_vars class_ref_tc in
              let tc_nb_keeps = Table.get_ind_nb_sign_keeps class_ref_tc in
              let tc_promoted =
                List.filteri (fun i _ -> i >= tc_nb_keeps) tc_ip_vars
              in
              List.map
                (fun var_name ->
                  let qualified_ty =
                    Tqualified (Tvar (0, Some tc_name), var_name)
                  in
                  ( Fnested_using (var_name, qualified_ty),
                    VPublic,
                    SNoTag ) )
                tc_promoted
            | _ -> [] )
          template_params
      in
      (* Collect names already covered by TC-promoted usings (from
         constructor body).  These take priority over forwarded usings
         because they carry the computed type expression rather than
         a simple forward from the template parameter. *)
      let tc_promoted_names =
        List.filter_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (id, _) -> Some id
            | _ -> None )
          tc_promoted_usings
      in
      (* Remove forwarded usings that are superseded by TC-promoted usings *)
      let forwarded_usings =
        List.filter
          (fun (f, _, _) ->
            match f with
            | Fnested_using (id, _) ->
              not (List.exists (Id.equal id) tc_promoted_names)
            | _ -> true )
          forwarded_usings
      in
      (* Collect names already covered by forwarded usings. *)
      let forwarded_names =
        List.filter_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (id, _) -> Some id
            | _ -> None )
          forwarded_usings
      in
      (* Generate [using VarName = ConcreteType;] for each promoted
         variable that has a known, non-self-referential concrete type
         and is not already covered by a forwarded using.  Use
         zip-up-to-minimum so that partially-extractable Records
         still get declarations for the extractable promoted vars. *)
      let concrete_usings =
        let n =
          min (List.length promoted_vars) (List.length promoted_concrete_types)
        in
        List.init n (fun i ->
            let var_name = List.nth promoted_vars i in
            let concrete_ml_ty = List.nth promoted_concrete_types i in
            let concrete_cpp_ty =
              convert_ml_type_to_cpp_type
                base_env
                type_var_names
                concrete_ml_ty
            in
            (var_name, concrete_cpp_ty) )
        |> List.filter_map (fun (var_name, concrete_cpp_ty) ->
               if
                 List.exists (Id.equal var_name) tc_promoted_names
                 || List.exists (Id.equal var_name) forwarded_names
                 || is_self_referential_promoted var_name concrete_cpp_ty
               then
                 None
               else
                 Some
                   ( Fnested_using (var_name, concrete_cpp_ty),
                     VPublic,
                     SNoTag ) )
      in
      (* Exclude promoted type args from the returned list (used for
         static_assert) *)
      let non_promoted_type_args =
        List.filteri (fun i _ -> i < nb_sign_keeps_for_promoted) type_args
      in
      (* Generate nested promoted-var usings.  When a using aliases a
         typeclass-typed field (e.g., [using base_category = nat_category;]),
         we must also forward the promoted vars of that typeclass so that
         method return types resolve correctly.  E.g., if [base_category]
         satisfies [PreCategory] with promoted [Obj], generate
         [using Obj = typename base_category::Obj;]. *)
      let direct_usings =
        tc_promoted_usings @ forwarded_usings @ concrete_usings
      in
      let direct_names =
        List.filter_map
          (fun (f, _, _) ->
            match f with Fnested_using (id, _) -> Some id | _ -> None)
          direct_usings
      in
      let nested_promoted_usings =
        List.concat_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (using_name, _using_ty) ->
              (* Find this field's ML type in the typeclass definition *)
              let field_ml_ty =
                List.find_map
                  (fun (fld_opt, fml_ty) ->
                    match fld_opt with
                    | Some fld_ref ->
                      let fld_name_str =
                        Common.pp_global_name Term fld_ref
                      in
                      if String.equal fld_name_str (Id.to_string using_name)
                      then Some fml_ty
                      else None
                    | None -> None)
                  fields_with_types
              in
              ( match field_ml_ty with
              | Some (Miniml.Tglob (tc_ref, _, _))
                when Table.is_typeclass tc_ref ->
                let nested_ip = Table.get_ind_ip_vars tc_ref in
                let nested_nk = Table.get_ind_nb_sign_keeps tc_ref in
                let nested_promoted =
                  List.filteri (fun i _ -> i >= nested_nk) nested_ip
                in
                List.filter_map
                  (fun v ->
                    if List.exists (Id.equal v) direct_names then None
                    else
                      Some
                        ( Fnested_using
                            ( v,
                              Tqualified
                                (Tvar (0, Some using_name), v) ),
                          VPublic,
                          SNoTag ))
                  nested_promoted
              | _ -> [] )
            | _ -> [])
          direct_usings
      in
      let all_usings = direct_usings @ nested_promoted_usings in
      if methods = [] && all_usings = [] then
        (None, Some class_ref, non_promoted_type_args)
      else
        let decl =
          Dstruct
            {
              ds_ref = name;
              ds_fields = all_usings @ methods;
              ds_tparams = template_params;
              ds_constraint = None;
              ds_needs_shared_from_this = false;
            }
        in
        (Some decl, Some class_ref, non_promoted_type_args)
    | _ -> (None, Some class_ref, type_args) )
  | _ -> (None, None, [])

(** Check if a term is a type class instance (constructs a type class record) *)
let is_typeclass_instance (_body : ml_ast) (ty : ml_type) : bool =
  match ml_return_type ty with
  | Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false

(** Parse a custom template string to find which [%tN] positions are
    referenced.  Returns the set of 0-based indices that appear in the
    template.  E.g. ["std::shared_ptr<ITree<%t1>>"] returns [{1}]. *)
let template_referenced_positions template_str =
  let len = String.length template_str in
  let rec scan i acc =
    if i > len - 3 then acc
    else if template_str.[i] = '%' && template_str.[i + 1] = 't' then
      let digit_start = i + 2 in
      let rec find_digit_end j =
        if j < len && template_str.[j] >= '0' && template_str.[j] <= '9' then
          find_digit_end (j + 1)
        else j
      in
      let digit_end = find_digit_end digit_start in
      if digit_end > digit_start then
        let idx =
          int_of_string
            (String.sub template_str digit_start (digit_end - digit_start))
        in
        scan digit_end (IntSet.add idx acc)
      else scan (i + 1) acc
    else scan (i + 1) acc
  in
  scan 0 IntSet.empty

(** For a custom/monad GlobRef, return the set of type-arg positions that
    appear in its template string.  Returns [None] if no custom template
    exists or the template is empty (all positions are implicitly
    referenced). *)
let custom_referenced_positions_opt g =
  let check_template = function
    | Some s when s <> "" -> Some (template_referenced_positions s)
    | _ -> None
  in
  match check_template (Table.get_monad_template_opt g) with
  | Some _ as r -> r
  | None -> check_template (Table.find_custom_opt g)

(** Collect (index, name) pairs for all Tvar occurrences, sorted by index *)
let get_tvars_indexed t =
  let get_name i n =
    match n with
    | None -> tvar_id i
    | Some n -> n
  in
  let rec aux l = function
    | Tvar (1000, _) ->
      (* Promoted type var marker from a Record-turned-TypeClass.  These
         represent projected type members (e.g., [Obj] from [PreCategory])
         and must be resolved through typeclass instance access — not as
         standalone template parameters. *)
      l
    | Tvar (i, n) ->
      if List.exists (fun (x, _) -> i == x) l then
        l
      else
        (i, get_name i n) :: l
    | Tglob (_, tys, _) -> List.fold_left aux l tys
    | Tfun (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Tmod (_, ty) -> aux l ty
    | Tnamespace (_, ty) -> aux l ty
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | _ -> l
  in
  List.sort (fun (x, _) (y, _) -> Int.compare x y) (aux [] t)

(** Like [get_tvar_indices] but only collects tvars that will actually
    appear in the rendered C++ type.  For custom types with a template
    (e.g. [std::shared_ptr<ITree<%t1>>]), only type-arg positions
    referenced by the template are visited.  Unreferenced positions hold
    phantom tvars (e.g. E in [itree E R] where the template only uses
    [%t1] = R) that the C++ compiler cannot deduce. *)
let get_rendered_tvar_indices t =
  let rec aux l = function
    | Tvar (1000, _) -> l
    | Tvar (i, _) ->
      if List.mem i l then l else i :: l
    | Tglob (g, tys, _) ->
      let tys_to_visit =
        match custom_referenced_positions_opt g with
        | Some referenced ->
          List.filteri (fun i _ -> IntSet.mem i referenced) tys
        | None -> tys
      in
      List.fold_left aux l tys_to_visit
    | Tfun (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Tmod (_, ty) -> aux l ty
    | Tnamespace (_, ty) -> aux l ty
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | _ -> l
  in
  aux [] t

(** Tvar names, sorted by index *)
let get_tvars t = List.map snd (get_tvars_indexed t)

(** Tvar indices only (unsorted) *)
let get_tvar_indices t = List.map fst (get_tvars_indexed t)

(** Collect tvar indices that are represented concretely in the generated C++
    signature.

    In addition to the codomain and non-function domain parameters, tvars from
    fully rendered function signatures are primary: {!gen_dfun} can represent
    those signatures with [is_invocable_r_v] constraints.  This matters for a
    type such as [(B -> C) -> (A -> B) -> A -> C], where [B] occurs only in
    function-typed parameters but is nevertheless a real part of both callable
    signatures.

    Function types containing HKT erasure markers cannot be rendered faithfully.
    If any function parameter is HKT-erased, function-only tvars remain phantom:
    conversion may already have removed their occurrences from the erased
    function, so it is no longer possible to correlate them safely with tvars in
    the remaining clean functions.  This preserves the defaults needed by
    [hk_map].  Tvars that also occur in the codomain or a non-function parameter
    remain primary.

    Used by both {!gen_dfun} (to choose between an [is_invocable_r_v]
    constraint and plain [TTtypename]) and {!phantom_aware_temps} (to choose
    whether a template parameter needs a [void] default). *)
let primary_tvar_indices dom cod =
  let add_rendered acc t =
    List.fold_left
      (fun acc i -> IntSet.add i acc)
      acc
      (get_rendered_tvar_indices t)
  in
  let concrete, clean_fun, has_erased_fun =
    List.fold_left
      (fun (concrete, clean_fun, has_erased_fun) t ->
        match t with
        | Tfun _ when has_hkt_erasure t ->
          (concrete, clean_fun, true)
        | Tfun _ ->
          (concrete, add_rendered clean_fun t, has_erased_fun)
        | _ ->
          (add_rendered concrete t, clean_fun, has_erased_fun) )
      (add_rendered IntSet.empty cod, IntSet.empty, false)
      dom
  in
  if has_erased_fun then concrete else IntSet.union concrete clean_fun

(** Collect tvar indices that appear in type INDEX positions of inductives
    in the ML type.  Type indices are stripped from the C++ type by
    {!convert_ml_type_to_cpp_type} but may be needed in function bodies
    for [any_cast] when matching on type-indexed inductives with
    wholesale-erased fields.

    Only collects tvars from inductives where [get_ind_num_param_vars_opt]
    succeeds and the number of type args exceeds the parameter count
    (indicating genuine indices, not parameters). *)
let collect_ml_type_index_tvars ml_ty =
  let result = ref IntSet.empty in
  let rec collect_tvars = function
    | Miniml.Tvar i | Miniml.Tvar' i ->
      result := IntSet.add i !result
    | Miniml.Tarr (t1, t2) ->
      collect_tvars t1; collect_tvars t2
    | Miniml.Tglob (_, ts, _) ->
      List.iter collect_tvars ts
    | Miniml.Tmeta {contents = Some t} -> collect_tvars t
    | _ -> ()
  in
  let rec walk = function
    | Miniml.Tarr (t1, t2) -> walk t1; walk t2
    | Miniml.Tglob (g, ts, _) ->
      ( match g with
      | GlobRef.IndRef (kn, _) ->
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars when num_param_vars < List.length ts ->
          List.iteri (fun i t ->
            if i >= num_param_vars then collect_tvars t
          ) ts
        | _ -> () );
        List.iter walk ts
      | _ -> List.iter walk ts )
    | Miniml.Tmeta {contents = Some t} -> walk t
    | _ -> ()
  in
  walk ml_ty;
  !result

(** Build template parameter list with phantom detection.

    Type variables represented concretely in the generated signature (i.e.
    {!primary_tvar_indices}) are emitted as plain [typename T].  All others —
    phantom tvars from erased HKT positions or custom-template positions that
    the C++ compiler cannot deduce — are emitted with a [void] default
    ([typename T = void]).

    We never {i remove} tvars from the list: only default them.  Removing
    would shift the de Bruijn index-to-name mapping used throughout the
    pipeline (see {!convert_ml_type_to_cpp_type}).

    @param force_required  Set of tvar indices that must be required (plain
      [typename T]) even if they don't appear in the C++ function type.
      Used for type INDEX tvars that are stripped from the C++ type but needed
      for [any_cast] in function bodies. *)
let phantom_aware_temps ?(force_required = IntSet.empty) cty tvars =
  match cty with
  | Tfun (dom, cod) ->
    let tvars_indexed = get_tvars_indexed cty in
    let primary = primary_tvar_indices dom cod in
    let primary = IntSet.union primary force_required in
    let extra =
      IntSet.fold (fun i acc ->
        if List.exists (fun (j, _) -> j = i) tvars_indexed then acc
        else (i, tvar_id i) :: acc
      ) force_required []
    in
    let all_tvars_indexed =
      List.sort (fun (x, _) (y, _) -> Int.compare x y)
        (tvars_indexed @ extra)
    in
    List.map
      (fun (i, id) ->
        if IntSet.mem i primary then
          (TTtypename, id)
        else
          (TTtypename_default Tvoid, id) )
      all_tvars_indexed
  | _ -> List.map (fun id -> (TTtypename, id)) tvars

(** Substitute [CPPglob id] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion. *)
let rec glob_subst_expr (id : GlobRef.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPglob (id', _, _) when globref_equal id id' ->
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
    | Tvar (i, None) ->
      (try Tvar (i, Some (List.nth tvars (pred i))) with Failure _ -> ty)
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
  (* Determine itree extraction mode from the monad template string.
     Reified mode preserves [itree E R] as [shared_ptr<ITree<R>>]; sequential
     mode erases to [R].  We detect reified by checking whether the monad
     template contains "ITree" (e.g. ["std::shared_ptr<ITree<%t1>>"]).
     Must be set BEFORE void-ification so the mode is available. *)
  let saved_mode = tctx.itree_mode in
  ( match extract_monad_from_codomain ty with
  | Some monad_ref ->
    tctx.itree_mode <-
      (if is_monad_reified monad_ref then Reified else Sequential)
  | None -> () );
  (* Void-ify unit codomain: unit as return type maps to C++ void.
     Check the ML result type (unwrapping monad if present) to determine
     if the function returns unit. Then recursively replace the unit enum
     with Tvoid in the C++ codomain type.
     - Sequential mode: Unit → void directly (the monad wrapper is erased,
       so the C++ function literally returns void)
     - Reified mode: Tglob(itree, [E; Unit]) → Tglob(itree, [E; void])
       (printed as shared_ptr<ITree<void>> via monad template) *)
  let unit_void =
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty)
  in
  let cod = apply_unit_void unit_void (tctx.itree_mode = Reified) cod in
  let rec get_dom l ty =
    match ty with
    | Tarr (t1, t2) -> get_dom (t1 :: l) t2
    | _ -> l
  in
  let mldom = get_dom [] ty in
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
  (* Replace Tunknown in body param types with corresponding sig types. This
     handles promoted dependent records where the lambda's type annotation has
     Tunknown for the erased carrier, while the function signature has
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
  let ids =
    if List.length ids = List.length sig_types_for_ids then
      List.map2
        (fun (id, body_ty) sig_ty ->
          if count_ml_arrows body_ty > count_ml_arrows sig_ty then
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
        | (Miniml.Tvar i | Miniml.Tvar' i), _
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
          | (Miniml.Tvar i | Miniml.Tvar' i), _
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
  (* Detect which function-typed parameters are NOT simply forwarded at
     self-recursive call sites.  These are excluded from template-parameter
     promotion below — they keep their [Tmod(TMconst, Tfun(dom, cod))] type
     which prints as [const std::function<R(Args...)>].

     [detect_non_forwarded_params] returns source-order indices (param 0 =
     first Rocq parameter).  We need two index-checking helpers because the
     parameter list [ids] is in de Bruijn order (innermost first = last source
     param first), while [List.rev ids] is in source order:

     Source order (Rocq): p0 p1 p2 indices 0, 1, 2 De Bruijn order (ids): p2 p1
     p0 indices 0, 1, 2

     So non-forwarded source index [i] maps to de Bruijn index [n_ids - 1 - i]. *)
  let non_fwd_param_indices = detect_non_forwarded_params n (List.length ids) b in
  let non_fwd_set = IntSet.of_list non_fwd_param_indices in
  let is_non_fwd_param_source i = IntSet.mem i non_fwd_set in
  let n_ids = List.length ids in
  let is_non_fwd_param_db i = IntSet.mem (n_ids - 1 - i) non_fwd_set in
  let all_params = missing @ ids in
  (* Type class instance parameters become C++ template type parameters. We
     assign unique names (_tcI0, _tcI1, ...) to avoid collision with: - User
     variable names like 'i', 'j', etc. - Other generated names in the same
     scope The original parameter order is preserved for correct de Bruijn
     indexing. *)
  let typeclass_counter = ref 0 in
  let typeclass_temps = ref [] in
  let all_params_for_env =
    List.map
      (fun (ml_id, ty) ->
        if Table.is_typeclass_type ty then (
          let i = !typeclass_counter in
          typeclass_counter := i + 1;
          let instance_name = tc_instance_id i in
          (* Build template param info.  Use [TTconcept] for unary
             concepts (nb_sign_keeps = 0) so the C++ compiler enforces
             concept satisfaction, e.g. [PreCategory _tcI0] instead of
             [typename _tcI0]. Multi-parameter concepts cannot use inline
             syntax because extra type args aren't available at the
             template-param declaration site. *)
          let temp_info =
            match ty with
            | Miniml.Tglob (class_ref, type_args, _) ->
              let type_arg_cpp =
                List.map
                  (fun t ->
                    convert_ml_type_to_cpp_type
                      (empty_env ())
                      []
                      t )
                  type_args
              in
              let tt =
                let nb_keeps = Table.get_ind_nb_sign_keeps class_ref in
                if nb_keeps = 0 then TTconcept (class_ref, [])
                else TTconcept (class_ref, type_arg_cpp)
              in
              ( tt,
                instance_name,
                Some (class_ref, type_arg_cpp),
                remove_prime_id (id_of_mlid ml_id) )
            | _ ->
              ( TTtypename,
                instance_name,
                None,
                remove_prime_id (id_of_mlid ml_id) )
          in
          typeclass_temps := temp_info :: !typeclass_temps;
          (* Return renamed param for env (use instance_name like 'i' instead of
             original name) *)
          (instance_name, ty) )
        else (* Regular param: keep original name *)
          (remove_prime_id (id_of_mlid ml_id), ty) )
      all_params
  in
  let typeclass_temps = List.rev !typeclass_temps in
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
         Converts to [Tvar(1000, Some "m_carrier")] ← needs resolution

       This map provides the resolution:
         "m_carrier" ↦ Tqualified(Tvar(0, Some "_tcI0"), "m_carrier")
         Which prints as: typename _tcI0::m_carrier

     For nested typeclasses (e.g., PreStableCategory has a base_category : PreCategory),
     promoted vars are doubly qualified:
       "Obj" ↦ typename _tcI0::base_category::Obj

     The map is applied by [resolve_promoted_in_type] to substitute all
     [Tvar(1000, ...)] markers with their qualified forms. *)
  let promoted_var_resolutions =
    List.concat_map (fun (_tt, tc_name, class_info, _) ->
      match class_info with
      | Some (class_ref, _) ->
        let ip_vars = Table.get_ind_ip_vars class_ref in
        let nb_keeps = Table.get_ind_nb_sign_keeps class_ref in
        let promoted = List.filteri (fun i _ -> i >= nb_keeps) ip_vars in
        (* Direct promoted vars: Var → typename _tcI0::Var *)
        let direct =
          List.map (fun var_name ->
            (var_name, Tqualified (Tvar (0, Some tc_name), var_name))
          ) promoted
        in
        (* Nested promoted vars from TC-typed fields:
           Var → typename _tcI0::field::Var *)
        let method_list =
          let fields = Table.get_record_fields class_ref in
          let field_types = Table.record_field_types class_ref in
          let non_dummy =
            filter_value_types field_types
          in
          if List.length fields = List.length non_dummy then
            List.combine fields non_dummy
          else []
        in
        let nested =
          List.concat_map (fun (field_opt, field_ty) ->
            match (field_opt, field_ty) with
            | Some field_ref, Miniml.Tglob (r, _, _)
              when Table.is_typeclass r ->
              let field_name_str = Common.pp_global_name Term field_ref in
              let field_id = Id.of_string field_name_str in
              if List.exists (Id.equal field_id) promoted then
                let n_ip = Table.get_ind_ip_vars r in
                let n_nk = Table.get_ind_nb_sign_keeps r in
                let n_promoted =
                  List.filteri (fun i _ -> i >= n_nk) n_ip
                in
                List.filter_map (fun nested_var ->
                  (* Skip if already directly mapped (direct takes priority) *)
                  if List.exists (Id.equal nested_var) promoted then None
                  else
                    Some (nested_var,
                      Tqualified
                        (Tqualified (Tvar (0, Some tc_name), field_id),
                         nested_var))
                ) n_promoted
              else []
            | _ -> []
          ) method_list
        in
        direct @ nested
      | None -> []
    ) typeclass_temps
  in
  (* Substitute promoted type var markers [Tvar(1000, Some name)] with their
     qualified resolutions throughout a C++ type tree. *)
  let rec resolve_promoted_in_type ty =
    match ty with
    | Tvar (1000, Some name) -> (
      match List.find_opt
              (fun (n, _) -> Id.equal n name)
              promoted_var_resolutions with
      | Some (_, resolved) -> resolved
      | None -> ty )
    | Tglob (r, tys, es) ->
      Tglob (r, List.map resolve_promoted_in_type tys, es)
    | Tfun (doms, cod) ->
      Tfun (List.map resolve_promoted_in_type doms,
            resolve_promoted_in_type cod)
    | Tmod (m, t) -> Tmod (m, resolve_promoted_in_type t)
    | Tref t -> Tref (resolve_promoted_in_type t)
    | Tshared_ptr t -> Tshared_ptr (resolve_promoted_in_type t)
    | Tvariant ts -> Tvariant (List.map resolve_promoted_in_type ts)
    | Tqualified (b, id) -> Tqualified (resolve_promoted_in_type b, id)
    | Tnamespace (r, t) -> Tnamespace (r, resolve_promoted_in_type t)
    | Tid (id, ts) -> Tid (id, List.map resolve_promoted_in_type ts)
    | Tid_external (id, ts) -> Tid_external (id, List.map resolve_promoted_in_type ts)
    | Tptr t -> Tptr (resolve_promoted_in_type t)
    | _ -> ty
  in
  (* Apply promoted var resolution to domain and codomain types *)
  let dom =
    if promoted_var_resolutions <> [] then
      List.map resolve_promoted_in_type dom
    else dom
  in
  let cod =
    if promoted_var_resolutions <> [] then
      resolve_promoted_in_type cod
    else cod
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
  push_env_types all_ids;
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
          if promoted_var_resolutions <> [] then
            resolve_promoted_in_type cpp_ty
          else cpp_ty
        in
        (* Reify monadic parameter types: itree E R → shared_ptr<ITree<R>> *)
        let cpp_ty = reify_monadic_param_type ty cpp_ty in
        let wrapped = wrap_param_by_ownership ~is_owned:owned cpp_ty in
        (x, wrapped) )
      ids_with_owned
  in
  (* Promote forwarded function-typed parameters to C++ template parameters.

     Function-typed parameters (those with C++ type [Tmod(TMconst, Tfun(...))])
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
     type parameters that were filtered out as phantom by gen_decl_for_pp.
     Similarly, function-typed params containing HKT erasure markers (Tany
     or dummy_type) also get TTtypename, since their type structure has been
     partially erased and an is_invocable_v constraint would be malformed. *)
  let primary = primary_tvar_indices dom cod in
  let unwrap_fun_ty2 = function
    | Tmod (TMconst, (Tfun _ as f)) -> Some f
    | Tfun _ as f -> Some f
    | _ -> None
  in
  let fun_tys =
    List.filter_map
      (fun (x, ty, i) ->
        match unwrap_fun_ty2 ty with
        | Some (Tfun (fdom, fcod)) when not (is_non_fwd_param_source i) ->
          let fun_idx = get_tvar_indices (Tfun (fdom, fcod)) in
          let has_undeclared =
            List.exists (fun idx -> not (IntSet.mem idx primary)) fun_idx
          in
          if has_undeclared || has_hkt_erasure (Tfun (fdom, fcod)) then
            Some (x, TTtypename, fun_tparam_id i)
          else
            let fcod = if is_cpp_unit_type fcod then Tvoid else fcod in
            Some (x, TTfun (fdom, fcod), fun_tparam_id i)
        | _ -> None )
      (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids))
  in
  (* Replace the parameter type of promoted (forwarded) function params with the
     template type variable [F&&]. Non-forwarded params are left untouched — they
     keep [Tmod(TMconst, Tfun(dom, cod))] which prints as [const
     std::function<R(Args...)>]. This loop iterates [ids] which is in de Bruijn
     order, so we use [is_non_fwd_param_db] for the guard. *)
  let ids =
    List.mapi
      (fun i (x, ty) ->
        match unwrap_fun_ty2 ty with
        | Some (Tfun _) when not (is_non_fwd_param_db i) ->
          ( x,
            Tref
              (Tref (Tvar (0, Some (fun_tparam_id (List.length ids - i - 1)))))
          )
        | _ -> (x, ty) )
      ids
  in
  (* Add type class instance template parameters - instance types come first *)
  let typeclass_temps_basic =
    List.map (fun (tt, id, _, _) -> (tt, id)) typeclass_temps
  in
  (* Build recursive call reference with typeclass and type params only.
     Function type params (from fun_tys) are excluded because they should be
     deduced from arguments, not explicitly specified in recursive calls. *)
  let rec_call_temps = typeclass_temps_basic @ temps in
  let rec_call =
    mk_cppglob n (List.map (fun (_, id) -> Tvar (0, Some id)) rec_call_temps)
  in
  (* Combine all template params for function signature. Save the non-typeclass
     type params for Tvar index resolution below. *)
  let regular_temps = temps @ List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let temps = typeclass_temps_basic @ regular_temps in
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
        | TTtypename | TTtypename_default _ -> Some id
        | _ -> None )
      regular_temps
  in
  set_current_type_vars type_var_ids;
  set_current_param_types all_ids;
  (* Activate promoted var resolution for body generation — types like
     [Tvar(1000, Some "Obj")] in type annotations will be resolved to
     qualified access through the typeclass instance chain. *)
  let saved_promoted_var_map = tctx.promoted_var_map in
  tctx.promoted_var_map <- promoted_var_resolutions;
  (* Set the outer function name so inner fixpoints can generate lifted names *)
  let saved_outer_name = tctx.current_outer_function_name in
  tctx.current_outer_function_name <- Some (Common.pp_global_name Term n);
  (* Check if the return type is coinductive - if so, wrap body in lazy thunk *)
  let ml_ret = ml_return_type ty in
  let is_cofix_return = Table.is_coinductive_type ml_ret in
  (* For cofixpoints, wrap the return expression in Type::lazy_([=]() ->
     ret_ty { ... }) *)
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
        CPPqualified
          (mk_cppglob coind_ref type_args, Id.of_string "lazy_")
      in
      let thunk = CPPlambda ([], Some ret_cpp, [Sreturn (Some x)], true) in
      Sreturn (Some (CPPfun_call (lazy_factory, [thunk])))
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
      (* outermost param first *)
      (* Substitute %0, %1, ... placeholders with actual parameter names *)
      let subst_placeholders template =
        let result = ref template in
        Array.iteri
          (fun i (id, _) ->
            let placeholder = Printf.sprintf "%%%d" i in
            let replacement = Id.to_string id in
            let buf = Buffer.create (String.length !result) in
            let s = !result in
            let len = String.length s in
            let plen = String.length placeholder in
            let j = ref 0 in
            while !j < len do
              if !j <= len - plen && String.sub s !j plen = placeholder then (
                Buffer.add_string buf replacement;
                j := !j + plen )
              else (
                Buffer.add_char buf s.[!j];
                j := !j + 1 )
            done;
            result := Buffer.contents buf )
          all_id_arr;
        !result
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
              let expr_str = subst_placeholders template in
              Some (Sassert (expr_str, Some expr_str))
            | Table.AssertComment comment ->
              Some (Sassert ("true", Some comment)) )
        assertions
  in
  tctx.current_letin_depth <- 0;
  tctx.match_param_counter <- 0;
  tctx.cs_counter <- 0;
  (* Phase 2: Initialize owned-variable tracking for move insertion. Parameters
     at de Bruijn indices 1..n_params; owned ones get added to the set. *)
  let n_all_params = List.length all_params in
  tctx.move_n_params <- n_all_params;
  tctx.move_owned_vars <-
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
      (List.mapi (fun i o -> (i, o)) owned_flags);
  tctx.move_dead_after <- Escape.IntSet.empty;
  (* Expose the C++ return type to inner call sites so they can recover erased
     template type args (see try_recover_erased_return_type). *)
  let saved_return_type = tctx.current_cpp_return_type in
  tctx.current_cpp_return_type <- Some cod;
  (* For non-inlined custom constants (axioms mapped via Crane Extract
     Constant), generate a forwarding body that delegates to the custom
     implementation instead of the default CPPabort throw. *)
  let custom_forwarding_body =
    match b with
    | MLaxiom _ when is_custom n && not (to_inline n) ->
      let custom_name = find_custom n in
      let param_vars = List.rev_map (fun (id, _) -> CPPvar id) ids in
      Some [Sreturn (Some (CPPfun_call (CPPraw custom_name, param_vars)))]
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
            List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap b)
          in
          return_captures_by_value b
      in
      (* State-threading optimization: when the return type is [pair<S, R>]
         and there is a value parameter of type [S], insert [std::move] at
         every recursive self-call and every [make_pair] return so that the
         state value is moved rather than deep-copied at each recursion level.
         This turns O(L * N) total copies into O(L) moves. *)
      let ids, b =
        let rec strip_ns = function Tmod (_, t) | Tnamespace (_, t) -> strip_ns t | t -> t in
        match strip_ns cod with
        | Tglob (g, s_ty :: _, _) when is_prod_global g -> (
          match
            List.find_opt
              (fun (_, ty) -> cpp_ty_eq (match ty with Tmod (TMconst, t) -> t | t -> t) s_ty)
              ids
          with
          | Some (state_id, _) ->
            rewrite_state_threading_moves n state_id s_ty ids b
          | None -> (ids, b) )
        | _ -> (ids, b)
      in
      clear_current_type_vars ();
      clear_current_param_types ();
      let guard = build_guard_compare_stmts n ids in
      Dfundef ([(n, [])], cod, ids, guard @ sigma_asserts @ b, no_pure) )
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
            (gen_stmts env cofix_wrap (MLapp (lifted_b, args)))
      in
      let b = return_captures_by_value b in
      (* let b = List.map forward_fun_args b in *)
      clear_current_type_vars ();
      clear_current_param_types ();
      let guard = build_guard_compare_stmts n ids in
      Dfundef ([(n, [])], cod, ids, guard @ sigma_asserts @ b, no_pure)
  in
  tctx.current_cpp_return_type <- saved_return_type;
  tctx.current_outer_function_name <- saved_outer_name;
  tctx.promoted_var_map <- saved_promoted_var_map;
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
          let int_ty = Tvar (0, Some (Id.of_string "int")) in
          let rec void_return_to_zero = function
            | Sreturn None -> Sreturn (Some (CPPint 0))
            | Sif (c, t, e) ->
              Sif (c, List.map void_return_to_zero t,
                      List.map void_return_to_zero e)
            | Sblock ss -> Sblock (List.map void_return_to_zero ss)
            | Smatch (branches, default) ->
              Smatch
                ( List.map
                    (fun br ->
                      { br with smb_body = List.map void_return_to_zero br.smb_body })
                    branches,
                  Option.map (List.map void_return_to_zero) default )
            | s -> s
          in
          ( match inner with
          | Dfundef (names, _cod, params, body, flags) ->
            Dfundef (names, int_ty, params, List.map void_return_to_zero body, flags)
          | d -> d )
        | None, true ->
          (* Case 3: top-level reified — rename to [_main], register for
             wrapper that calls [_main()->run()] *)
          let new_label = Label.of_id (Id.of_string "_main") in
          let new_n = GlobRef.ConstRef (Constant.make2 (Constant.modpath c) new_label) in
          Table.set_main_function (Id.of_string "_main") (ml_codomain ty) None needs_run;
          ( match inner with
          | Dfundef (_, cod, params, body, flags) ->
            Dfundef ([(new_n, [])], cod, params, body, flags)
          | d -> d )
      end else
        inner
    | _ -> inner
  in
  (* Restore saved itree mode *)
  tctx.itree_mode <- saved_mode;
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
         (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
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
  let inner = Dfundecl ([(n, [])], cod, params, false) in
  match temps with
  | [] -> (inner, env)
  | l -> (Dtemplate (l, None, inner), env)

(** Build a map from erased field projection GlobRefs to their Tvar index for a
    promoted dependent record / typeclass. Returns [(GlobRef.t * int) list]
    where int is the 1-based Tvar index. *)
let erased_proj_tvar_map (class_ref : GlobRef.t) : (GlobRef.t * int) list =
  let open GlobRef in
  match class_ref with
  | IndRef (kn, _) | ConstructRef ((kn, _), _) ->
    let promoted_vars = Table.get_ind_ip_vars class_ref in
    if promoted_vars = [] then
      []
    else
      let mp = MutInd.modpath kn in
      let n_promoted = List.length promoted_vars in
      List.mapi
        (fun i var_id ->
          let knp = Constant.make2 mp (Label.of_id var_id) in
          (ConstRef knp, n_promoted - i) )
        promoted_vars
  | _ -> []

(** Expand TC-typed carrier refs to their nested Type-valued promoted vars.

    When a typeclass has a promoted field whose ML type is itself a typeclass
    (e.g., [base_category : PreCategory] in [PreStableCategory]),
    [erased_proj_tvar_map] returns a reference to the TC-typed field (e.g.,
    [ConstRef base_category]).  Using that directly in [rewrite_ml_ast_types]
    produces the wrong C++ type — [typename _tcI0::base_category] instead of
    [typename _tcI0::base_category::Obj].

    This function replaces TC-typed carrier refs with the Type-valued promoted
    vars of the nested typeclass.  Expansion is recursive: if the nested TC
    itself has TC-typed promoted vars, they are expanded further.

    @param class_ref  The containing typeclass (e.g., [PreStableCategory])
    @param carrier_refs  The list from [erased_proj_tvar_map] *)
let rec expand_tc_typed_carriers
    (class_ref : GlobRef.t)
    (carrier_refs : (GlobRef.t * int) list)
    : (GlobRef.t * int) list =
  let fields = Table.get_record_fields class_ref in
  let field_types = Table.record_field_types class_ref in
  let non_dummy =
    filter_value_types field_types
  in
  if List.length fields <> List.length non_dummy then
    carrier_refs
  else
    let field_type_pairs = List.combine fields non_dummy in
    let expanded =
      List.concat_map (fun (ref, idx) ->
        let ref_name = Common.pp_global_name Common.Term ref in
        match List.find_opt (fun (fopt, _) ->
          match fopt with
          | Some fr -> Common.pp_global_name Common.Term fr = ref_name
          | None -> false
        ) field_type_pairs with
        | Some (_, Miniml.Tglob (r, _, _)) when Table.is_typeclass r ->
          (* TC-typed carrier — expand to the nested TC's promoted vars *)
          let nested = erased_proj_tvar_map r in
          if nested = [] then [(ref, idx)]
          else expand_tc_typed_carriers r nested
        | _ -> [(ref, idx)]
      ) carrier_refs
    in
    (* Sort by ascending tvar index so the first-declared field (lowest
       index) comes first.  [erased_proj_tvar_map] assigns index
       [n_promoted - i], so field 0 gets index 1 (lowest).  This matters
       because [rewrite_ml_ast_types] uses [List.hd] to pick the carrier. *)
    List.sort (fun (_, i1) (_, i2) -> compare i1 i2) expanded

(** Replace Tglob references to erased projections with Tvar' in an ML type. *)
let rec replace_erased_proj_refs
    (proj_map : (GlobRef.t * int) list)
    (t : ml_type) : ml_type =
  let find_in_map r =
    List.find_map
      (fun (ref, idx) -> if GlobRef.CanOrd.equal r ref then Some idx else None)
      proj_map
  in
  match t with
  | Miniml.Tglob (r, ts, args) ->
    ( match find_in_map r with
    | Some idx -> Miniml.Tvar' idx
    | None ->
      let ts' = List.map (replace_erased_proj_refs proj_map) ts in
      if ts == ts' then t else Miniml.Tglob (r, ts', args) )
  | Miniml.Tarr (t1, t2) ->
    let t1' = replace_erased_proj_refs proj_map t1 in
    let t2' = replace_erased_proj_refs proj_map t2 in
    if t1 == t1' && t2 == t2' then t else Miniml.Tarr (t1', t2')
  | Miniml.Tunknown -> Miniml.Tvar' 1
  | _ -> t

(** Replace Tunknown in all type annotations within an ML AST body with the
    GlobRef of the first promoted type var (the carrier). This allows
    convert_ml_type_to_cpp_type to detect it as a promoted type var.
    [carrier_refs] is a list of (GlobRef.t * int) from erased_proj_tvar_map. *)
let rec rewrite_ml_ast_types
    (carrier_refs : (GlobRef.t * int) list)
    (ast : ml_ast) : ml_ast =
  if carrier_refs = [] then
    ast
  else
    let carrier_ref = fst (List.hd carrier_refs) in
    let rec rty t =
      match t with
      | Miniml.Tunknown -> Miniml.Tglob (carrier_ref, [], [])
      | Miniml.Tmeta ({contents = Some inner} as meta) ->
        let inner' = rty inner in
        if inner != inner' then meta.contents <- Some inner';
        t
      | Miniml.Tmeta ({contents = None} as meta) ->
        (* Unresolved meta — resolve to carrier *)
        meta.contents <- Some (Miniml.Tglob (carrier_ref, [], []));
        t
      | Miniml.Tarr (t1, t2) -> Miniml.Tarr (rty t1, rty t2)
      | Miniml.Tglob (r, ts, a) ->
        let ts' = List.map rty ts in
        Miniml.Tglob (r, ts', a)
      | _ -> t
    in
    let rast = rewrite_ml_ast_types carrier_refs in
    match ast with
    | MLlam (id, ty, body) -> MLlam (id, rty ty, rast body)
    | MLletin (id, ty, e1, e2) -> MLletin (id, rty ty, rast e1, rast e2)
    | MLglob (r, tys) -> MLglob (r, List.map rty tys)
    | MLcons (ty, r, args) -> MLcons (rty ty, r, List.map rast args)
    | MLtuple es -> MLtuple (List.map rast es)
    | MLcase (ty, scrut, branches) ->
      let branches' =
        Array.map
          (fun (binds, bty, pat, body) ->
            let binds' = List.map (fun (id, t) -> (id, rty t)) binds in
            (binds', rty bty, pat, rast body) )
          branches
      in
      MLcase (rty ty, rast scrut, branches')
    | MLfix (i, name_types, bodies, is_cofix) ->
      let name_types' = Array.map (fun (id, ty) -> (id, rty ty)) name_types in
      let bodies' = Array.map rast bodies in
      MLfix (i, name_types', bodies', is_cofix)
    | MLapp (f, args) -> MLapp (rast f, List.map rast args)
    | MLmagic e -> MLmagic (rast e)
    | MLrel _
     |MLdummy _
     |MLaxiom _
     |MLexn _
     |MLuint _
     |MLfloat _
     |MLparray _
     |MLstring _ -> ast

(** Rewrite projection types for promoted dependent records. When a function's
    first parameter is a promoted typeclass (e.g., Magma), and the remaining
    args/return have erased carrier refs, replace them with Tvar references from
    the typeclass's field types.

    The function name [n] is used to find which field of the typeclass this
    projection corresponds to. *)
let rewrite_typeclass_projection_type (n : GlobRef.t) (ty : ml_type) : ml_type =
  match ty with
  | Tarr ((Tglob (class_ref, _, _) as tc_arg), rest)
    when Table.is_typeclass class_ref ->
    let fields = Table.get_record_fields class_ref in
    let field_types = Table.record_field_types class_ref in
    let proj_map = erased_proj_tvar_map class_ref in
    if proj_map <> [] then (* Check if n is a projection of this typeclass *)
      let non_dummy_types =
        filter_value_types field_types
      in
      let non_dummy_fields_types =
        if List.length fields = List.length non_dummy_types then
          List.combine fields non_dummy_types
        else
          List.map (fun f -> (f, Miniml.Tunknown)) fields
      in
      let proj_name = Common.pp_global_name Term n in
      let matching_field_type =
        List.find_map
          (fun (field_ref_opt, ft) ->
            match field_ref_opt with
            | Some fr when Common.pp_global_name Term fr = proj_name -> Some ft
            | _ -> None )
          non_dummy_fields_types
      in
      match matching_field_type with
      | Some field_ty -> Tarr (tc_arg, field_ty)
      | None -> Tarr (tc_arg, replace_erased_proj_refs proj_map rest)
    else
      ty
  | _ -> ty

(** Get the erased projection map for a function's type, if it takes a promoted
    typeclass as first argument. *)
let get_erased_proj_map_from_type (ty : ml_type) : (GlobRef.t * int) list =
  match ty with
  | Tarr (Tglob (class_ref, _, _), _) when Table.is_typeclass class_ref ->
    erased_proj_tvar_map class_ref
  | _ -> []

(** Generate C++ declaration from ML definition (main entry point) *)
let gen_decl n b ty =
  (* Set itree extraction mode early — before type conversion — so that
     reify_monadic_param_type (called inside convert_ml_type_to_cpp_type)
     can correctly voidify unit result types in ITree parameters. *)
  let saved_mode = tctx.itree_mode in
  ( match extract_monad_from_codomain ty with
  | Some monad_ref ->
    tctx.itree_mode <-
      (if is_monad_reified monad_ref then Reified else Sequential)
  | None -> () );
  let saved_method_ns = set_method_ns_for_locals () in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  let result =
    match cty with
    | Tfun _ ->
      let f, env = gen_dfun n b cty ty temps in
      (f, env, tvars)
    | _ ->
    match b with
    | MLaxiom _ ->
      (* Axiom values become zero-arg functions that throw std::logic_error when
         called. This avoids throwing during static initialization (which
         terminates the program before main). *)
      let body_expr = gen_expr (empty_env ()) b in
      let inner = Dfundef ([(n, [])], cty, [], [Sreturn (Some body_expr)], false) in
      ( match temps with
      | [] -> (inner, empty_env (), tvars)
      | l -> (Dtemplate (l, None, inner), empty_env (), tvars) )
    | _ ->
      let saved_return_type = tctx.current_cpp_return_type in
      tctx.current_cpp_return_type <- Some cty;
      tctx.cs_counter <- 0;
      let body_expr = gen_expr (empty_env ()) b in
      tctx.current_cpp_return_type <- saved_return_type;
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
            CPPfun_call (
              CPPlambda ([], None,
                [Sexpr body_expr; Sreturn (Some (mk_tt_expr ()))],
                false),
              [])
        else body_expr
      in
      let inner = Dasgn (n, cty, body_expr) in
      ( match temps with
      | [] -> (inner, empty_env (), tvars)
      | l -> (Dtemplate (l, None, inner), empty_env (), tvars) )
  in
  tctx.method_self_ns <- saved_method_ns;
  tctx.itree_mode <- saved_mode;
  result

(** Generate C++ declaration with pretty-printing adjustments *)
let gen_decl_for_pp n b ty =
  let carrier_refs = get_erased_proj_map_from_type ty in
  (* Expand TC-typed carrier refs: when a carrier ref points to a
     typeclass-typed promoted field (e.g., base_category : PreCategory),
     replace it with the nested TC's Type-valued promoted vars (e.g., Obj).
     This ensures rewrite_ml_ast_types replaces Tunknown with the actual
     type-level field rather than the struct-level typeclass field. *)
  let carrier_refs =
    match ty with
    | Miniml.Tarr (Miniml.Tglob (class_ref, _, _), _)
      when Table.is_typeclass class_ref ->
      expand_tc_typed_carriers class_ref carrier_refs
    | _ -> carrier_refs
  in
  let b = rewrite_ml_ast_types carrier_refs b in
  let b = resolve_body_tvars b ty in
  let saved_method_ns = set_method_ns_for_locals () in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars cty in
  (* Count typeclass-typed parameters in the ML domain — these become template
     params inside gen_dfun but aren't reflected in tvars (which comes from the
     C++ type). We need tvars to be non-empty when typeclass params exist so
     callers use the full Dtemplate definition. *)
  let tc_param_ids =
    match ty with
    | Tarr _ -> collect_typeclass_param_ids ty
    | _ -> []
  in
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
  let temps = phantom_aware_temps ~force_required:index_tvar_set cty tvars in
  let result = match cty with
  | Tfun (dom, _) ->
    let f, e = gen_dfun n b cty ty temps in
    let fun_tys =
      List.filter_map
        (fun (ty, i) ->
          match ty with
          | Tfun _ -> Some (fun_tparam_id i)
          | _ -> None )
        (List.mapi (fun i ty -> (ty, i)) dom)
    in
    let tvars = tc_param_ids @ tvars @ fun_tys in
    (Some f, e, tvars)
  | _ ->
  match b with
  | MLaxiom _ ->
    (* Axiom values: generate as zero-arg function so they throw when called,
       not at static init time *)
    let body_expr = gen_expr (empty_env ()) b in
    let inner = Dfundef ([(n, [])], cty, [], [Sreturn (Some body_expr)], false) in
    let ds =
      match temps with
      | [] -> inner
      | l -> Dtemplate (l, None, inner)
    in
    (Some ds, empty_env (), tc_param_ids @ tvars)
  | _ -> (None, empty_env (), tc_param_ids @ tvars)
  in
  tctx.method_self_ns <- saved_method_ns;
  result

(** Generate a full C++ function definition for a [Dfix] member.

    Simplifies the ML type, resolves promoted carrier references in the body,
    converts to C++ types, and delegates to {!gen_dfun} for the actual
    definition.  Returns [(decl, env, tvars)]. *)
let gen_dfun_def n b ty =
  (* Simplify the ML type to resolve metavariables before converting to C++ *)
  let ty = type_simpl ty in
  (* Rewrite Tunknown in body types to promoted carrier refs. This allows
     convert_ml_type_to_cpp_type to resolve them correctly. *)
  let carrier_refs = get_erased_proj_map_from_type ty in
  let b = rewrite_ml_ast_types carrier_refs b in
  let b = resolve_body_tvars b ty in
  let saved_method_ns = set_method_ns_for_locals () in
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
  let temps = phantom_aware_temps ~force_required:index_tvar_set cty tvars in
  (* Count typeclass-typed parameters in the ML domain — these become template
     params inside gen_dfun but aren't reflected in tvars (which comes from the
     C++ type). We need tvars to be non-empty when typeclass params exist so
     callers (gen_dfuns_header) use the full Dtemplate definition. *)
  let tc_param_ids =
    match ty with
    | Tarr _ -> collect_typeclass_param_ids ty
    | _ -> []
  in
  match cty with
  | Tfun (dom, _) ->
    let f, env = gen_dfun n b cty ty temps in
    let fun_tys =
      List.filter_map
        (fun (ty, i) ->
          match ty with
          | Tfun _ -> Some (fun_tparam_id i)
          | _ -> None )
        (List.mapi (fun i ty -> (ty, i)) dom)
    in
    let tvars = tc_param_ids @ tvars @ fun_tys in
    tctx.method_self_ns <- saved_method_ns;
    (f, env, tvars)
  | _ ->
    let f, env = gen_dfun n b cty ty temps in
    tctx.method_self_ns <- saved_method_ns;
    (f, env, tc_param_ids @ tvars)

(** Generate C++ function specification (for header files) *)
let gen_spec n b ty =
  let ty = type_simpl ty in
  let ml_ty = ty in  (* preserve ML type before C++ conversion *)
  let unit_void =
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty) in
  let is_reified = unit_void &&
    (match extract_monad_from_codomain ty with
     | Some mr -> is_monad_reified mr | None -> false) in
  let saved_method_ns = set_method_ns_for_locals () in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  let result =
    match ty with
    | Tfun (dom, cod) ->
      let cod = apply_unit_void unit_void is_reified cod in
      gen_sfun n b dom cod temps
    | _ ->
    match b with
    | MLaxiom _ ->
      (* Axiom values: generate as zero-arg function declaration *)
      let inner = Dfundef ([(n, [])], ty, [], [], false) in
      ( match temps with
      | [] -> (inner, empty_env ())
      | l -> (Dtemplate (l, None, inner), empty_env ()) )
    | _ ->
      (* Expose the constant's C++ type so that inner call sites can recover
         erased template type args (see try_recover_erased_return_type). Without
         this, calls like pick<natBoxed>() inside a constant body cannot deduce
         the missing type parameter. *)
      let saved_return_type = tctx.current_cpp_return_type in
      tctx.current_cpp_return_type <- Some ty;
      (* Strip MLmagic wrapper and track whether a type coercion from std::any
         is needed.  MLmagic wraps expressions when the extraction detects a
         type mismatch (e.g. Obj = std::any vs nat = unsigned int). *)
      let has_magic, inner_body =
        match b with
        | MLmagic inner -> (true, inner)
        | _ -> (false, b)
      in
      (* The optimization pass (simpl) transforms MLmagic(MLapp(f, args)) into
         MLapp(MLmagic(f), args), pushing the magic inside the application head.
         Detect this so we still insert std::any_cast for the result. *)
      let has_magic =
        has_magic || ml_head_has_magic b
      in
      tctx.cs_counter <- 0;
      let b_expr = gen_expr (empty_env ()) inner_body in
      tctx.current_cpp_return_type <- saved_return_type;
      (* Wrap with std::any_cast when the C++ expression returns std::any but the
         declared type is concrete.  Two detection paths:
         (a) MLmagic — the extraction explicitly flagged a type coercion.
         (b) Record field projection — the field's return type is a promoted
             type var (erased to std::any) but Coq's type system sees the
             concrete type, so no MLmagic is generated. *)
      let is_concrete_target =
        match ty with
        | Tany | Tvar _ | Tunknown | Tvoid | Ttodo | Tauto -> false
        | Tglob (g, _, _) when Table.is_erased_type_const g -> false
        | _ -> not (type_is_erased ty)
      in
      let needs_any_cast =
        is_concrete_target
        && (has_magic || ml_body_returns_erased_field inner_body)
      in
      let b_expr =
        if needs_any_cast then CPPany_cast (ty, b_expr) else b_expr
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
            CPPfun_call (
              CPPlambda ([], None,
                [Sexpr b_expr; Sreturn (Some (mk_tt_expr ()))],
                false),
              [])
        else b_expr
      in
      let inner = Dasgn (n, Tmod (TMconst, ty), b_expr) in
      ( match temps with
      | [] -> (inner, empty_env ())
      | l -> (Dtemplate (l, None, inner), empty_env ()) )
  in
  tctx.method_self_ns <- saved_method_ns;
  result

(** Generate a C++ forward declaration (spec) for a struct-level function.

    Produces a simpler signature than {!gen_dfun_def} — suitable for use in
    struct bodies where the full definition is not needed. *)
let gen_sfun_spec n b ty =
  let ty = type_simpl ty in
  let unit_void =
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty) in
  let is_reified = unit_void &&
    (match extract_monad_from_codomain ty with
     | Some mr -> is_monad_reified mr | None -> false) in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match ty with
  | Tfun (dom, cod) ->
    let cod = apply_unit_void unit_void is_reified cod in
    gen_sfun n b dom cod temps
  | _ ->
    let ty = apply_unit_void unit_void is_reified ty in
    gen_sfun n b [Tvoid] ty temps

(** Generate multiple function definitions *)
let gen_dfuns (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let result = gen_dfun_def name bs.(i) tys.(i) in
      (* Discard lifted declarations here - they are template functions that
         belong only in the header file (.h), not the source file (.cpp).
         gen_dfuns_header will collect them for the header. *)
      ignore (take_lifted_decls ());
      [result] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Convert a Dfundef (definition with body) to a Dfundecl (declaration without
    body). Recursively handles Dtemplate wrappers. Used to generate forward
    declarations that match the full definition's signature (including concept
    constraints). *)
let rec decl_to_spec (d : cpp_decl) : cpp_decl =
  match d with
  | Dfundef (ids, ret_ty, params, body, no_pure) ->
    let no_pure = no_pure ||
      match body with
      | [Sreturn (Some (CPPabort _))] -> true
      | _ -> false
    in
    Dfundecl
      (ids, ret_ty, List.map (fun (id, ty) -> (Some id, ty)) params, no_pure)
  | Dtemplate (temps, cstr, inner) -> Dtemplate (temps, cstr, decl_to_spec inner)
  | _ -> d (* Already a declaration, return as-is *)

(** Generate function declarations for header files *)
let gen_dfuns_header (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let ds, env, tvars = gen_dfun_def name bs.(i) tys.(i) in
      let lifted = take_lifted_decls () in
      let lifted_results = List.map (fun d -> (d, empty_env ())) lifted in
      (* For non-template functions, derive the spec from the definition via
         decl_to_spec to ensure parameter types (owned vs borrowed) match
         exactly between the forward declaration and the out-of-line definition.
         Previously used gen_sfun_spec which ran independent escape
         analysis and could produce different ownership decisions. *)
      let main_result =
        match tvars with
        | [] -> (decl_to_spec ds, env)
        | _ :: _ -> (ds, env)
      in
      lifted_results @ [main_result] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Generate forward declarations (specs) for a group of mutually recursive
    functions, using the SAME signature as the full definitions. This ensures
    the specs match the out-of-line definitions (including concept-constrained
    template parameters). Unlike gen_dfuns_header which may use
    gen_sfun_spec (producing simpler signatures), this always derives the
    spec from gen_dfun_def. *)
let gen_dfuns_spec (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let ds, _env, _tvars = gen_dfun_def name bs.(i) tys.(i) in
      ignore (take_lifted_decls ());
      [(decl_to_spec ds, empty_env ())] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Generate both spec and def for a group of mutually recursive functions in
    one pass. Calls gen_dfun_def ONCE per function, then derives:
    - spec: decl_to_spec of the full definition (forward declaration)
    - def: the full definition (for templates) or None (for non-templates in
      header mode) Returns list of (spec, def_option, lifted_decls) *)
let gen_dfuns_dual ~is_header (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let ds, env, tvars = gen_dfun_def name bs.(i) tys.(i) in
      let lifted = take_lifted_decls () in
      let spec = (decl_to_spec ds, env) in
      let def =
        match (tvars, is_header) with
        | _ :: _, true -> Some (ds, env) (* Template + header: full def in .h *)
        | _ :: _, false -> None (* Template + source: already in .h *)
        | [], true -> None (* Non-template + header: def goes in .cpp *)
        | [], false -> Some (ds, env)
        (* Non-template + source: full def in .cpp *)
      in
      [(spec, def, lifted)] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Generate both spec and def for a single Dterm function in one pass. Calls
    gen_decl_for_pp ONCE, then derives both spec and def. Returns (spec_opt,
    def_opt, tvars) *)
let gen_decl_for_pp_dual ~is_header n b ty =
  let ds_opt, env, tvars = gen_decl_for_pp n b ty in
  match (ds_opt, tvars) with
  | Some ds, _ :: _ ->
    (* Template function: spec is decl_to_spec, def only in header *)
    let def = if is_header then Some (ds, env) else None in
    (Some (decl_to_spec ds, env), def, tvars)
  | Some ds, [] ->
    (* Non-template function: spec via decl_to_spec to ensure parameter types
       (owned vs borrowed) match exactly between declaration and definition.
       Using gen_spec here would run independent escape analysis that may
       produce different ownership decisions than gen_dfun used for the def. *)
    let def = if is_header then None else Some (ds, env) in
    (Some (decl_to_spec ds, env), def, tvars)
  | None, _ ->
    (* Non-function type: no def needed *)
    let spec_ds, spec_env = gen_spec n b ty in
    (Some (spec_ds, spec_env), None, tvars)

let rec replace_return_this_expr inner_ty = function
  | CPPthis -> CPPshared_from_this inner_ty
  | CPPlambda (params, ret, body, cap) ->
    CPPlambda
      (params, ret, List.map (replace_return_this_stmt inner_ty) body, cap)
  | CPPfun_call (f, args) ->
    CPPfun_call
      ( replace_return_this_expr inner_ty f,
        List.map (replace_return_this_expr inner_ty) args )
  | CPPoverloaded exprs ->
    CPPoverloaded (List.map (replace_return_this_expr inner_ty) exprs)
  | e -> e

(** Statement-level counterpart of {!replace_return_this_expr}: recurses into
    if/switch/match branches to replace [return this] with [shared_from_this]. *)
and replace_return_this_stmt inner_ty = function
  | Sreturn (Some e) -> Sreturn (Some (replace_return_this_expr inner_ty e))
  | Sif (cond, then_stmts, else_stmts) ->
    Sif
      ( cond,
        List.map (replace_return_this_stmt inner_ty) then_stmts,
        List.map (replace_return_this_stmt inner_ty) else_stmts )
  | Scustom_case (ty, scrut, tys, brs, tag) ->
    Scustom_case
      ( ty,
        scrut,
        tys,
        List.map
          (fun (binds, br_ty, stmts) ->
            (binds, br_ty, List.map (replace_return_this_stmt inner_ty) stmts) )
          brs,
        tag )
  | Sswitch (scrut, ind, brs, default) ->
    Sswitch
      ( scrut,
        ind,
        List.map
          (fun (ctor, stmts) ->
            (ctor, List.map (replace_return_this_stmt inner_ty) stmts) )
          brs,
        Option.map (List.map (replace_return_this_stmt inner_ty)) default )
  | Smatch (branches, default) ->
    Smatch
      ( List.map
          (fun br ->
            { br with
              smb_body =
                List.map (replace_return_this_stmt inner_ty) br.smb_body
            })
          branches,
        Option.map (List.map (replace_return_this_stmt inner_ty)) default )
  | Sexpr e -> Sexpr (replace_return_this_expr inner_ty e)
  | s -> s

(** Replace [CPPthis] with [CPPderef CPPthis] in return positions for value-type
    methods.  When a method returns a value type (not shared_ptr), [return this;]
    is invalid because [this] is a pointer.  We need [return *this;] instead. *)
let rec deref_return_this_expr = function
  | CPPthis -> CPPderef CPPthis
  | CPPlambda (params, ret, body, cap) ->
    CPPlambda (params, ret, List.map deref_return_this_stmt body, cap)
  | CPPfun_call (f, args) ->
    CPPfun_call (deref_return_this_expr f,
                 List.map deref_return_this_expr args)
  | CPPoverloaded exprs ->
    CPPoverloaded (List.map deref_return_this_expr exprs)
  | e -> e

and deref_return_this_stmt s =
  ( match s with
  | _ -> () );
  match s with
  | Sreturn (Some e) -> Sreturn (Some (deref_return_this_expr e))
  | Sif (cond, then_stmts, else_stmts) ->
    Sif (cond,
         List.map deref_return_this_stmt then_stmts,
         List.map deref_return_this_stmt else_stmts)
  | Scustom_case (ty, scrut, tys, brs, tag) ->
    Scustom_case (ty, scrut, tys,
      List.map (fun (binds, br_ty, stmts) ->
        (binds, br_ty, List.map deref_return_this_stmt stmts)) brs,
      tag)
  | Sswitch (scrut, ind, brs, default) ->
    Sswitch (scrut, ind,
      List.map (fun (ctor, stmts) ->
        (ctor, List.map deref_return_this_stmt stmts)) brs,
      Option.map (List.map deref_return_this_stmt) default)
  | Smatch (branches, default) ->
    Smatch (List.map (fun br ->
        { br with smb_body = List.map deref_return_this_stmt br.smb_body })
      branches,
      Option.map (List.map deref_return_this_stmt) default)
  | Sexpr e -> Sexpr (deref_return_this_expr e)
  | s -> s

(** Prevent dangling [this] in by-value lambda captures.

    When a methodified function contains a by-value lambda that references
    [this], the lambda may escape the method scope (returned through
    [option], [pair], record, etc.).  The raw [this] pointer dangles once
    the caller's [shared_ptr] is released.

    Fix: bind [shared_from_this()] to a local [_self] at the top of the
    method body, then replace [CPPthis] inside every by-value lambda body
    with [CPPvar "_self"].  The lambda's [=] capture picks up [_self] as
    a [shared_ptr] copy that keeps the object alive.  The outer method
    body keeps raw [CPPthis] for direct method calls (safe because the
    method is invoked on a live object). *)
let replace_this_in_lambdas self_type stmts =
  let id_type ty = ty in
  let self_id = Id.of_string "_self" in
  (* Check if CPPthis or CPPshared_from_this appears in an expression. *)
  let rec expr_has_this = function
    | CPPthis | CPPshared_from_this _ -> true
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if expr_has_this e' then found := true; e') (fun s -> s) id_type e);
      !found
  in
  (* Check if CPPthis or CPPshared_from_this appears in statements. *)
  let rec stmt_has_this = function
    | s ->
      let found = ref false in
      ignore (map_stmt
        (fun e -> if expr_has_this e then found := true; e)
        (fun s' -> if stmt_has_this s' then found := true; s')
        id_type s);
      !found
  in
  let stmts_have_this stmts = List.exists stmt_has_this stmts in
  (* Check if any by-value lambda in the method body captures this. *)
  let rec lambda_captures_this_expr = function
    | CPPlambda (_, _, body, true) -> stmts_have_this body
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if lambda_captures_this_expr e' then found := true; e')
        (fun s ->
          if lambda_captures_this_stmt s then found := true; s)
        id_type e);
      !found
  and lambda_captures_this_stmt s =
    let found = ref false in
    ignore (map_stmt
      (fun e -> if lambda_captures_this_expr e then found := true; e)
      (fun s' -> if lambda_captures_this_stmt s' then found := true; s')
      id_type s);
    !found
  in
  let needs_self = List.exists lambda_captures_this_stmt stmts in
  if not needs_self then stmts
  else
    (* Determine whether _self is a value type (non-enum).
       Coinductives and regular inductives are both value types. *)
    let is_value_self =
      match self_type with
      | Tglob (self_ref, _, _) -> not (is_enum_inductive self_ref)
      | _ -> false
    in
    (* For value-type methods, the loopifier uses "_self" as the name for the
       receiver pointer (const T *_self = this / _f._self).  Using the same
       name for the value copy would cause a redefinition conflict in loopified
       methods.  Use "_self_val" for the value copy to avoid the clash. *)
    let self_id = if is_value_self then Id.of_string "_self_val" else self_id in
    (* Substitute CPPthis and CPPshared_from_this → CPPvar self_id inside
       by-value lambda bodies.  For value-type _self_val, also collapse
       CPPderef(CPPthis) → CPPvar self_id to avoid dereferencing a value. *)
    let rec subst_expr = function
      | CPPderef (CPPthis | CPPshared_from_this _) when is_value_self ->
        CPPvar self_id
      | CPPthis | CPPshared_from_this _ -> CPPvar self_id
      | e -> map_expr subst_expr subst_stmt id_type e
    and subst_stmt s =
      map_stmt subst_expr subst_stmt id_type s
    in
    let rec walk_expr = function
      | CPPlambda (params, ret, body, true) ->
        CPPlambda (params, ret, List.map subst_stmt body, true)
      | e -> map_expr walk_expr walk_stmt id_type e
    and walk_stmt s =
      map_stmt walk_expr walk_stmt id_type s
    in
    let self_expr, self_ty =
      if is_value_self then
        (CPPderef CPPthis, Some self_type)
      else
        (CPPshared_from_this self_type, Some (Tshared_ptr self_type))
    in
    let self_binding = Sasgn (self_id, self_ty, self_expr) in
    self_binding :: List.map walk_stmt stmts

(** Check if a C++ type contains [Tshared_ptr] anywhere in its structure.

    Recurses through [Tref], [Tmod], [Tshared_ptr], [Tptr], [Tid], [Tglob],
    [Tnamespace], and [Tfun] to find any nested [Tshared_ptr].

    Used in method generation to gate [replace_return_this_stmt]: the
    [return this] to [return shared_from_this()] transformation is only
    correct when the return type actually wraps the receiver in
    [shared_ptr] (e.g., [shared_ptr<T>] or [pair<shared_ptr<T>, V>]). *)
let rec contains_shared_ptr = function
  | Tshared_ptr _ -> true
  | Tref t | Tmod (_, t) | Tptr t -> contains_shared_ptr t
  | Tid (_, args) | Tid_external (_, args) | Tglob (_, args, _) ->
    List.exists contains_shared_ptr args
  | Tfun (args, ret) ->
    List.exists contains_shared_ptr args || contains_shared_ptr ret
  | _ -> false

(** Check if any expression or statement contains [CPPshared_from_this]. *)
let rec expr_has_shared_from_this = function
  | CPPshared_from_this _ -> true
  | CPPlambda (_, _, body, _) -> List.exists stmt_has_shared_from_this body
  | CPPfun_call (f, args) ->
    expr_has_shared_from_this f || List.exists expr_has_shared_from_this args
  | CPPoverloaded exprs -> List.exists expr_has_shared_from_this exprs
  | _ -> false

(** Statement-level counterpart of {!expr_has_shared_from_this}: checks whether
    any statement in a method body contains [CPPshared_from_this]. *)
and stmt_has_shared_from_this = function
  | Sreturn (Some e) -> expr_has_shared_from_this e
  | Sexpr e -> expr_has_shared_from_this e
  | Sif (_, then_stmts, else_stmts) ->
    List.exists stmt_has_shared_from_this then_stmts
    || List.exists stmt_has_shared_from_this else_stmts
  | Scustom_case (_, _, _, brs, _) ->
    List.exists
      (fun (_, _, stmts) -> List.exists stmt_has_shared_from_this stmts)
      brs
  | Sswitch (_, _, brs, default) ->
    List.exists
      (fun (_, stmts) -> List.exists stmt_has_shared_from_this stmts)
      brs
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Smatch (branches, default) ->
    List.exists
      (fun br -> List.exists stmt_has_shared_from_this br.smb_body)
      branches
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Sasgn (_, _, e) -> expr_has_shared_from_this e
  | _ -> false

(** Generate a single method for an inductive type from a method candidate.
    @param name     [GlobRef] of the containing inductive type
    @param vars     Template type variables of the containing inductive
    @param func_ref Rocq reference for the Rocq function being methodified
    @param body     ML body of the function
    @param ty       ML type of the function
    @param this_pos 0-based index of the [this] argument in the parameter list *)
let gen_single_method name vars (func_ref, body, ty, this_pos) =
  let num_ind_vars = List.length vars in
  let func_name = Id.of_string (Common.pp_global_name Term func_ref) in

  (* Get return type *)
  let all_args, ret_ty = get_args_and_ret [] ty in

  (* Determine the mapping from function type variables to inductive type
     variables. For same-module methods, the function uses Tvars 1..num_ind_vars
     for the inductive. For cross-module methods, the function may use different
     Tvar positions. We extract the actual mapping from the Tglob at this_pos.

     Example: fold_left has type (A → B → A) → list B → A → A where A=Tvar1
     (accumulator), B=Tvar2 (list element). list<B> uses Tvar2, so ind_tvar_map
     = [(2, 1)] meaning "Tvar2 → ind var position 1". Then Tvar1 is "extra" and
     becomes template param T1. *)
  let ind_tvar_map =
    match List.nth_opt all_args this_pos with
    | Some (Miniml.Tglob (_, tvar_args, _)) ->
      (* Extract Tvar indices from the Tglob args, paired with their position.
         Only include entries whose destination position is within the actual
         inductive type vars (1..num_ind_vars).  Type parameters killed during
         extraction (e.g., phantom params) produce Tglob args that map beyond
         the available vars — treat those as extra method tvars instead. *)
      List.filter (fun (_, dst) -> dst <= num_ind_vars)
        (List.concat
          (List.mapi
             (fun pos t ->
               match t with
               | Miniml.Tvar i | Miniml.Tvar' i -> [(i, pos + 1)]
               | _ -> [] )
             tvar_args ))
    | _ ->
      List.init num_ind_vars (fun i -> (i + 1, i + 1))
  in
  let ind_tvar_set = IntSet.of_list (List.map fst ind_tvar_map) in
  (* Remap ML type variables: assign canonical positions so
     convert_ml_type_to_cpp_type maps them correctly. - Inductive tvars →
     positions 1..num_ind_vars - Extra tvars → positions num_ind_vars+1,
     num_ind_vars+2, ... This avoids collisions when the function uses different
     numbering than the inductive.

     Example: fold_left has Tvar1 (accum), Tvar2 (list elem) ind_tvar_map = [(2,
     1)] — Tvar2 is the list element → position 1 extra tvars: [1] — Tvar1 is
     extra → position 2 (= num_ind_vars + 1) Full remap: Tvar1 → 2, Tvar2 → 1 *)
  let all_tvars = List.sort compare (collect_tvars [] ty) in
  let extra_tvars_orig =
    List.filter (fun i -> not (IntSet.mem i ind_tvar_set)) all_tvars
  in
  let needs_remap =
    (not (List.for_all (fun (src, dst) -> src = dst) ind_tvar_map))
    || extra_tvars_orig <> []
  in
  (* Build complete remap table: (original_idx → canonical_idx) *)
  let extra_remap =
    List.mapi (fun i orig -> (orig, num_ind_vars + 1 + i)) extra_tvars_orig
  in
  let full_remap = ind_tvar_map @ extra_remap in
  let remap_ml_tvar i =
    match List.assoc_opt i full_remap with
    | Some canonical -> canonical
    | None -> i
  in
  let rec remap_ml_type = function
    | Miniml.Tvar i -> Miniml.Tvar (remap_ml_tvar i)
    | Miniml.Tvar' i -> Miniml.Tvar' (remap_ml_tvar i)
    | Miniml.Tarr (t1, t2) -> Miniml.Tarr (remap_ml_type t1, remap_ml_type t2)
    | Miniml.Tglob (r, args, e) ->
      Miniml.Tglob (r, List.map remap_ml_type args, e)
    | Miniml.Tmeta {contents = Some t} -> remap_ml_type t
    | t -> t
  in
  let _ty = if needs_remap then remap_ml_type ty else ty in
  let ret_ty = if needs_remap then remap_ml_type ret_ty else ret_ty in
  let body =
    if needs_remap then Mlutil.remap_tvars remap_ml_tvar body else body
  in
  (* After remapping, extra tvars are at positions num_ind_vars+1,
     num_ind_vars+2, ... *)
  let extra_tvars = List.map snd extra_remap in
  let extra_tvar_names = List.mapi (fun i _ -> tvar_id (i + 1)) extra_tvars in
  let extra_tvar_map = List.combine extra_tvars extra_tvar_names in
  let subst_extra_tvars = make_subst_extra_tvars num_ind_vars extra_tvar_map in

  (* For type conversion in method contexts, use ns = {name} so that
     self-references INSIDE container types get shared_ptr wrapping
     (matching how struct fields are defined).  Then strip the top-level
     shared_ptr for the method's own type (value-type inductives are
     passed/returned by value, not by shared_ptr). *)
  let method_ns = Refset'.singleton name in
  let rec strip_self_ptr ty =
    match ty with
    | Tshared_ptr (Tglob (g, _, _)) when not (is_enum_inductive g) ->
      (match ty with Tshared_ptr inner -> inner | _ -> ty)
    | Tshared_ptr (Tglob (g, _, _)) when not (is_enum_inductive g) ->
      (match ty with Tshared_ptr inner -> inner | _ -> ty)
    | Tglob (r, args, es) ->
      Tglob (r, List.map strip_self_ptr args, es)
    | Tfun (args, ret) ->
      Tfun (List.map strip_self_ptr args, strip_self_ptr ret)
    | Tref t -> Tref (strip_self_ptr t)
    | Tmod (m, t) -> Tmod (m, strip_self_ptr t)
    | _ -> ty
  in
  let strip_top_level_self_ptr ty = strip_self_ptr ty in
  let ret_cpp =
    convert_ml_type_to_cpp_type (empty_env ()) ~ns:method_ns
      vars
      ret_ty
  in
  let ret_cpp = strip_top_level_self_ptr ret_cpp in
  let ret_cpp = subst_extra_tvars ret_cpp in

  (* Collect lambda parameters and build environment for de Bruijn lookup.
     push_vars' may rename duplicate parameters (e.g., two params named 't'
     become 't', 't0').

     We must use the renamed ids (all_ids) consistently for: 1. The environment
     - so gen_expr/gen_stmts produce correct variable references 2. The C++
     method signature - so parameter names match what the body references

     Previously, renamed ids were discarded and original names used for the
     signature, causing errors like: void method(tree t) { ... t0->v() ... }
     where 't0' in the body didn't exist as a parameter. *)
  let ids_with_types, inner_body = Mlutil.collect_lams body in
  (* Eta-expansion: if the body has fewer lambdas than the ML type's domain,
     add missing parameters (innermost first, named _x0, _x1, ...).
     This handles functions like [tree_to_adder : tree -> nat -> nat] where
     the body is a match expression returning closures rather than being
     directly lambda-wrapped.  Mirrors the same logic in gen_dfun. *)
  let rec get_method_dom l ty =
    match ty with
    | Tarr (t1, t2) -> get_method_dom (t1 :: l) t2
    | _ -> l
  in
  let mldom_for_eta = get_method_dom [] ty in
  let n_type_dom_eta = List.length mldom_for_eta in
  let n_body_dom_eta = List.length ids_with_types in
  let n_missing_eta = max 0 (n_type_dom_eta - n_body_dom_eta) in
  let ids_with_types, inner_body =
    if n_missing_eta = 0 then (ids_with_types, inner_body)
    else
      let missing_types = safe_firstn n_missing_eta mldom_for_eta in
      let n_miss = List.length missing_types in
      let missing =
        List.mapi
          (fun i t -> (Id (eta_param_id (n_miss - 1 - i)), t))
          missing_types
      in
      let lifted_b = ast_lift n_missing_eta inner_body in
      let args =
        List.rev
          (List.filter_map
             (fun (i, (_, t)) ->
               if isTdummy t then None else Some (MLrel (i + 1)) )
             (List.mapi (fun i x -> (i, x)) missing) )
      in
      (missing @ ids_with_types, MLapp (lifted_b, args))
  in
  let ids_converted =
    List.map
      (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
      ids_with_types
  in
  let all_ids, env = push_vars' ids_converted (empty_env ()) in
  reset_env_types ();
  push_env_types all_ids;
  (* Infer owned/borrowed for method parameters. Note: method 'this' is always
     borrowed (const method). *)
  let n_method_params = List.length ids_with_types in
  let method_owned_flags =
    let base = Escape.infer_owned_params n_method_params inner_body in
    let sub_esc = Escape.infer_sub_bindings_escape_params n_method_params inner_body in
    List.map2 (fun (b, s) (_, ty) ->
      b || (s && is_prod_ml_type ty))
      (List.combine base sub_esc) ids_with_types
  in

  (* Extract 'this' argument at this_pos - use renamed ids for consistency with
     body *)
  let ids_normal_order = List.rev all_ids in
  let this_arg_id_opt, param_ids_with_pos =
    Common.extract_at_pos
      this_pos
      (List.mapi (fun i (id, ty) -> (id, ty, i)) ids_normal_order)
  in
  let this_arg_id = Option.map (fun (id, _, _) -> id) this_arg_id_opt in
  let param_ids_with_pos =
    List.filter (fun (_, ty, _) -> not (ml_type_is_void ty)) param_ids_with_pos
  in

  (* Build owned flag lookup for non-this params. ids_normal_order is
     outermost-first. de Bruijn index of element i in normal order =
     n_method_params - i. method_owned_flags[db - 1] gives the owned flag. *)
  let get_param_owned_flag normal_order_idx =
    let db = n_method_params - normal_order_idx in
    match List.nth_opt method_owned_flags (db - 1) with
    | Some b -> b
    | None -> false
  in

  (* Convert params to C++ types.  Use method_ns so that self-references
     inside container types get shared_ptr (matching struct field types).
     Strip top-level shared_ptr since value-type params are bare values. *)
  let params_with_idx =
    List.mapi
      (fun i (id, ty, orig_idx) ->
        let cpp_ty =
          convert_ml_type_to_cpp_type env ~ns:method_ns
            vars
            ty
        in
        let cpp_ty = strip_top_level_self_ptr cpp_ty in
        let cpp_ty = subst_extra_tvars cpp_ty in
        let owned = get_param_owned_flag orig_idx in
        (id, cpp_ty, i, owned) )
      param_ids_with_pos
  in

  (* Extract function-typed parameters for template params *)
  let fun_params =
    List.filter_map
      (fun (id, cpp_ty, i, _) ->
        match cpp_ty with
        | Tfun (dom, cod) ->
          let cod = if is_cpp_unit_type cod then Tvoid else cod in
          Some (id, TTfun (dom, cod), fun_tparam_id i)
        | _ -> None )
      params_with_idx
  in

  (* Build template params *)
  let extra_type_params =
    List.map (fun name -> (TTtypename, name)) extra_tvar_names
  in
  let fun_template_params =
    List.map (fun (_, tt, fname) -> (tt, fname)) fun_params
  in
  let template_params = extra_type_params @ fun_template_params in

  (* Build final params with proper wrapping. Use escape analysis to determine
     owned vs borrowed: owned params are passed by value (for move semantics),
     borrowed params are passed by const ref. This matches gen_dfun's logic to
     ensure forward declarations and definitions agree. *)
  let params =
    List.map
      (fun (id, cpp_ty, i, owned) ->
        let wrapped =
          match cpp_ty with
          | Tfun _ -> Tref (Tref (Tvar (0, Some (fun_tparam_id i))))
          | _ -> wrap_param_by_ownership ~is_owned:owned cpp_ty
        in
        (id, wrapped) )
      params_with_idx
  in

  (* For coinductive return types, wrap return in lazy thunk *)
  let is_cofix_method = Table.is_coinductive_type ret_ty in
  let method_k x =
    if is_cofix_method then
      let type_args =
        match ret_ty with
        | Miniml.Tglob (_, args, _) ->
          List.map
            (fun t ->
              convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
                vars
                t )
            args
        | _ -> []
      in
      let coind_ref =
        match ret_ty with
        | Miniml.Tglob (r, _, _) -> r
        | _ ->
          CErrors.anomaly
            (Pp.str
               "gen_method_field: cofixpoint return type expected to be Tglob" )
      in
      let lazy_factory =
        CPPqualified
          (mk_cppglob coind_ref type_args, Id.of_string "lazy_")
      in
      let thunk = CPPlambda ([], Some ret_cpp, [Sreturn (Some x)], true) in
      Sreturn (Some (CPPfun_call (lazy_factory, [thunk])))
    else
      Sreturn (Some x)
  in
  (* Generate method body. Initialize move tracking for owned parameters.
     'this' is always borrowed (const method). *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let saved_type_vars = get_current_type_vars () in
  tctx.move_dead_after <- Escape.IntSet.empty;
  (* Initialize owned-variable tracking for method parameters.
     The de Bruijn environment has parameters in reverse order:
     ids_normal_order has outermost-first, push_vars' reverses them. *)
  let method_n_params = List.length ids_with_types in
  tctx.move_n_params <- method_n_params;
  (* method_owned_flags[i] corresponds to de Bruijn index i+1.
     db index i+1 maps to ids_with_types[i] (outermost-first, same order
     as push_vars' which prepends in list order).
     Only track ownership for non-trivial types (inductives). *)
  tctx.move_owned_vars <-
    List.fold_left
      (fun acc (i, owned) ->
        if owned then
          let ml_ty = snd (List.nth ids_with_types i) in
          if Escape.is_shared_ptr_type ml_ty
             || is_nontrivial_value_ml_type ml_ty then
            Escape.IntSet.add (i + 1) acc
          else acc
        else acc )
      Escape.IntSet.empty
      (List.mapi (fun i o -> (i, o)) method_owned_flags);
  tctx.match_param_counter <- 0;
  tctx.cs_counter <- 0;
  tctx.current_letin_depth <- 0;
  (* Set current type vars to include both the inductive's type vars and extra
     tvars. This ensures gen_expr/eta_fun correctly convert Tvars to named C++
     types when processing the method body (e.g., recursive calls carry type
     args). *)
  set_current_type_vars (vars @ extra_tvar_names);
  let saved_method_ns = tctx.method_self_ns in
  (* Include all local value-type inductives with recursive fields in the
     method ns.  This ensures that when the method body constructs or
     manipulates containers of recursive types (e.g. List<tree>), the
     type arguments get shared_ptr wrapping to match struct field types. *)
  let full_method_ns =
    List.fold_left
      (fun acc g ->
        if Table.has_recursive_fields g && not (is_enum_inductive g)
        then Refset'.add g acc
        else acc)
      method_ns
      (get_local_inductives ())
  in
  tctx.method_self_ns <- full_method_ns;
  let stmts = gen_stmts env method_k inner_body in
  tctx.method_self_ns <- saved_method_ns;
  set_current_type_vars saved_type_vars;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  (* Add type args to recursive self-calls. Inside fixpoint bodies, the
     extraction produces MLglob(func_ref, []) with empty type args for recursive
     references. When the function is a method, the recursive call needs
     explicit template args for non-deducible params. Replace CPPglob(func_ref,
     []) with CPPglob(func_ref, all_type_args).

     The type args must be in the ORIGINAL tys order (matching
     ind_tvar_positions used by pp_cpp_expr for filtering). Position i in tys
     corresponds to Tvar (i+1) in the original ML type. After remapping, Tvar
     (i+1) → remap_ml_tvar(i+1). We construct the C++ type arg from
     extended_vars at that remapped position. *)
  let extended_vars = vars @ extra_tvar_names in
  let all_method_type_args =
    List.filter_map
      (fun orig_tvar_idx ->
        let remapped = remap_ml_tvar orig_tvar_idx in
        if remapped - 1 >= List.length extended_vars then
          None
        else
          let name = List.nth extended_vars (remapped - 1) in
          Some (Tvar (remapped - 1, Some name)) )
      all_tvars
  in
  let stmts =
    if all_method_type_args <> [] then
      let self_call_with_tys = mk_cppglob func_ref all_method_type_args in
      List.map (glob_subst_stmt func_ref self_call_with_tys) stmts
    else
      stmts
  in
  let stmts =
    match this_arg_id with
    | Some id ->
      (* For value-type methods, substitute with [CPPderef CPPthis] so that
         return positions produce a value copy rather than a raw pointer.
         For shared_ptr/coinductive methods, keep bare [CPPthis]. *)
      let this_expr =
        if not (Table.is_coinductive name) && not (is_enum_inductive name) then
          CPPderef CPPthis
        else CPPthis
      in
      List.map (var_subst_stmt id this_expr) stmts
    | None -> stmts
  in
  (* Replace [CPPthis] with [CPPshared_from_this] in return expressions.  When a
     method body returns or stores [this] in a position that expects [shared_ptr]
     (e.g. [return this;], [return std::make_pair(this, this);]), the raw pointer
     cannot convert to [shared_ptr].  Using [shared_from_this()] produces a valid
     [shared_ptr] from the raw pointer.  Only applied when the return type
     contains [shared_ptr] (e.g. [shared_ptr<T>], [pair<shared_ptr, shared_ptr>])
     to avoid replacing [this] in method calls that just forward the receiver. *)
  (* Compute self_type unconditionally — needed by both return-this and
     lambda-this passes. *)
  let self_type_args =
    List.mapi (fun i vname -> Tvar (i, Some vname)) vars
  in
  let self_type = Tglob (name, self_type_args, []) in
  let stmts =
    if contains_shared_ptr ret_cpp then
      List.map (replace_return_this_stmt self_type) stmts
    else stmts
  in
  (* Replace [CPPthis] with [CPPshared_from_this] inside by-value lambda
     bodies.  When a method returns a closure that captures [this], the raw
     pointer would dangle after the caller's [shared_ptr] is released.
     Using [shared_from_this()] inside the lambda ensures the closure keeps
     the object alive. *)
  let stmts = return_captures_by_value stmts in
  let stmts = replace_this_in_lambdas self_type stmts in
  (* Apply tvar_subst_stmt with the extended vars list (defined above).
     extended_vars covers positions 1..num_ind_vars (inductive vars) and
     num_ind_vars+1, num_ind_vars+2, etc. (extra vars) so tvar_subst_stmt can
     name them all correctly. *)
  let stmts = List.map (tvar_subst_stmt extended_vars) stmts in

  let no_pure = is_monadic_ml_type ret_ty in
  (* Filter out phantom extra template params: if an extra tvar name doesn't
     appear in any param type or the return type, it's phantom (e.g., a killed
     inductive type arg) and shouldn't be a template param. *)
  let rec cpp_type_has_tvar name = function
    | Tvar (_, Some n) -> Id.equal n name
    | Tglob (_, args, _) | Tid (_, args) | Tid_external (_, args)
    | Tvariant args ->
      List.exists (cpp_type_has_tvar name) args
    | Tfun (args, ret) ->
      List.exists (cpp_type_has_tvar name) args || cpp_type_has_tvar name ret
    | Tref t | Tptr t | Tshared_ptr t | Tdecay t -> cpp_type_has_tvar name t
    | Tmod (_, t) | Tnamespace (_, t) -> cpp_type_has_tvar name t
    | Tqualified (base, _) -> cpp_type_has_tvar name base
    | _ -> false
  in
  let extra_tvar_name_set =
    List.fold_left (fun s n -> Id.Set.add n s) Id.Set.empty extra_tvar_names
  in
  let template_params =
    List.filter (fun (_tt, tname) ->
      if not (Id.Set.mem tname extra_tvar_name_set) then true
      else
        cpp_type_has_tvar tname ret_cpp
        || List.exists (fun (_, pty) -> cpp_type_has_tvar tname pty) params)
    template_params
  in
  let surviving_names =
    List.fold_left (fun s (_, n) -> Id.Set.add n s) Id.Set.empty template_params
  in
  let phantom_positions =
    List.filter_map (fun (orig_idx, name) ->
      if Id.Set.mem name extra_tvar_name_set
         && not (Id.Set.mem name surviving_names) then
        Some (orig_idx - 1)
      else None)
      (List.combine extra_tvars_orig extra_tvar_names)
  in
  if phantom_positions <> [] then
    Table.set_phantom_tvars func_ref phantom_positions;
  let phantom_name_set =
    List.fold_left (fun s (_, n) -> Id.Set.add n s) Id.Set.empty
      (List.filter (fun (_, n) ->
        Id.Set.mem n extra_tvar_name_set && not (Id.Set.mem n surviving_names))
        (List.combine extra_tvars_orig extra_tvar_names))
  in
  let rec strip_phantom_any_cast_expr e =
    let e = match e with
      | CPPany_cast (Tvar (_, Some name), inner) when Id.Set.mem name phantom_name_set ->
        strip_phantom_any_cast_expr inner
      | _ -> e
    in
    Minicpp.map_expr strip_phantom_any_cast_expr strip_phantom_any_cast_stmt (fun t -> t) e
  and strip_phantom_any_cast_stmt s =
    Minicpp.map_stmt strip_phantom_any_cast_expr strip_phantom_any_cast_stmt (fun t -> t) s
  in
  let stmts =
    if Id.Set.is_empty phantom_name_set then stmts
    else List.map strip_phantom_any_cast_stmt stmts
  in
  ( Fmethod
      {
        mf_name = func_name;
        mf_tparams = template_params;
        mf_ret_type = ret_cpp;
        mf_params = params;
        mf_body = stmts;
        mf_is_const = true;
        mf_is_static = false;
        mf_is_inline = false;
        mf_this_pos = this_pos;
        mf_no_pure = no_pure;
                  mf_is_noexcept = false;
      },
    VPublic,
    SNoTag )

(** Generate C++ header for an inductive type (v2 style: encapsulated struct
    with methods).

    Produces a self-contained struct with:
    - Nested constructor-alternative structs (e.g. [Leaf {}], [Node { ... }])
    - [using variant_t = std::variant<Leaf, Node>]
    - Private [variant_t d_v_] data member
    - Explicit constructors for each alternative
    - Static factory methods ([cons(...)], [cons_uptr(...)]) with move semantics
    - Methods from [method_candidates] (with [this] substitution)

    @param consarg_names  binder names from {!Miniml.ml_ind_packet.ip_consarg_names};
      when provided, constructor struct fields and factory parameters use
      descriptive names derived from the Rocq source instead of [d_a0] etc. *)

(** Does the ML type [ml_ty] contain [ind_ref] (or a mutual sibling) anywhere
    in its type arguments — but NOT at the top level?  Used to detect fields
    like [list(tree(A))] inside [tree]'s definition, which need field-level
    [shared_ptr] wrapping instead of type-argument wrapping. *)
let ml_type_has_nested_self_ref ~ind_ref ml_ty =
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
  let rec has_self_ref = function
    | Miniml.Tglob (r, args, _) ->
      is_self_or_mutual r || List.exists has_self_ref args
    | Miniml.Tmeta {contents = Some t} -> has_self_ref t
    | Miniml.Tarr (t1, t2) ->
      has_self_ref t1 || has_self_ref t2
    | _ -> false
  in
  match ml_ty with
  | Miniml.Tglob (r, args, _) when not (is_self_or_mutual r) ->
    List.exists has_self_ref args
  | Miniml.Tmeta {contents = Some (Miniml.Tglob (r, args, _))}
    when not (is_self_or_mutual r) ->
    List.exists has_self_ref args
  | _ -> false

(** Check whether the self/mutual reference inside [ml_ty] is uniform
    (i.e. its type arguments are exactly the parent's type parameters
    in order).  Non-uniform recursion needs [shared_ptr]. *)
let ml_self_ref_is_uniform ~ind_ref ~cname ml_ty =
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
  match find_self_ref_args ~is_self_or_mutual ml_ty with
  | Some args ->
    let n_params = Table.get_ctor_num_param_vars cname in
    List.length args = n_params
    && List.for_all (fun (j, arg) ->
      match arg with
      | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
      | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
      | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} -> k = j + 1
      | _ -> false
    ) (List.mapi (fun j a -> (j, a)) args)
  | None -> true

(** Generate the C++ struct definition for an inductive type.

    Produces one of three shapes depending on the inductive:
    - {b Value type}: a struct with an inner [std::variant] of constructor
      structs, factory methods, and [v()]/[v_mut()] accessors.
    - {b Shared-ptr type}: same struct wrapped in [std::shared_ptr] at use
      sites, with [shared_from_this] support and pointer-based destructors.
    - {b Enum}: a simple [enum class] with no variant or constructor structs.

    Major sections generated (in order): constructor structs, variant typedef,
    factory methods, iterative destructor (for recursive types),
    converting constructor (for mutual-inductive field-type differences),
    [operator==], and stream insertion.

    @param is_mutual     true when this type is part of a mutual block
    @param consarg_names field names from Rocq binders, indexed by constructor
    @param mutual_partners other types in the mutual block *)

let gen_ind_header_v2
    ?(is_mutual = false)
    ?(consarg_names = [||])
    ?(mutual_partners = [])
    vars
    name
    cnames
    tys
    method_candidates
    ind_kind =
  let is_coinductive = ind_kind = Coinductive in
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in

  (* Handle empty inductives (no constructors) - generate uninhabitable
     struct *)
  if Array.length cnames = 0 then
    (* For empty types like `Inductive empty : Type := .`, generate: struct
       empty { empty() = delete; }; This type cannot be constructed, matching
       the semantics of empty types. *)
    let method_fields =
      List.map (gen_single_method name vars) method_candidates
    in
    Dstruct
      {
        ds_ref = name;
        ds_fields = [(Fdeleted_ctor, VPublic, SNoTag)] @ method_fields;
        ds_tparams = templates;
        ds_constraint = None;
        ds_needs_shared_from_this = false;
      }
  else (* Check if all constructors are nullary: eligible for enum class *)
    let all_nullary = Array.for_all (fun tys_list -> tys_list = []) tys in
    if all_nullary && vars = [] && (not is_mutual) && not (is_custom name) then (
      (* Register as enum inductive for type/constructor/match generation *)
      Table.add_enum_inductive name;
      let ctor_names =
        Array.to_list
          (Array.map
             (fun c ->
               match c with
               | GlobRef.ConstructRef ((kn, i), cidx) ->
                 Id.of_string (Table.enum_ctor_name_of_ref kn i cidx)
               | _ -> ctor_fallback_id 0 )
             cnames )
      in
      let rocq_names =
        Array.to_list
          (Array.map
             (fun c ->
               match c with
               | GlobRef.ConstructRef _ -> Common.pp_global_name Type c
               | _ -> "" )
             cnames )
      in
      Denum
        {
          de_ref = name;
          de_ctors = ctor_names;
          de_ctor_rocq_names = rocq_names;
          de_tparams = [];
        } )
    else
      (* The main struct type: all inductives (including coinductives)
         are value types. *)
      let self_ty = Tglob (name, ty_vars, []) in
      let ind_type_name_str = Common.pp_global_name Type name in
      let n_ctors = Array.length cnames in

      (* Flat single-constructor check: no self-references in any field type,
         including transitive ones (e.g. custom_list<rose<A>>). *)
      let has_simple_self_ref_for_flat =
        Array.exists (List.exists (fun ty ->
          let rec check = function
            | Miniml.Tglob (r, args, _) ->
              globref_equal r name || List.exists check args
            | Miniml.Tmeta {contents = Some t} -> check t
            | _ -> false
          in check ty)) tys
      in
      let is_flat =
        n_ctors = 1 && not is_coinductive && mutual_partners = []
        && not has_simple_self_ref_for_flat
      in
      if is_flat then begin
        Table.add_flat_inductive name;
        let tys_list = tys.(0) in
        let c = cnames.(0) in
        let cname_str = ctor_struct_name_of_ref ~fallback_idx:0 c in
        let ctor_consarg_names =
          if 0 < Array.length consarg_names then consarg_names.(0) else [] in
        let n_fields = List.length tys_list in
        let field_ids =
          compute_and_register_field_names cname_str
            (augment_with_args_renaming c ctor_consarg_names)
            ctor_consarg_names n_fields in
        let erase_if_needed cpp_ty =
          if vars = [] then
            match cpp_ty with
            | Tshared_ptr _ -> tvar_erase_type cpp_ty
            | _ when has_unnamed_tvar cpp_ty -> Tany
            | _ -> cpp_ty
          else cpp_ty
        in
        let flat_fields =
          List.mapi (fun j ty ->
            let cpp_ty =
              erase_if_needed
                (convert_ml_type_to_cpp_type (empty_env ()) vars ty) in
            let field_id = List.nth field_ids j in
            (Fvar (field_id, cpp_ty), VPublic, SData)
          ) tys_list
        in
        let field_exprs = List.map (fun fid -> CPPvar fid) field_ids in
        let clone_body = [Sreturn (Some (CPPbraced field_exprs))] in
        let clone_field =
          ( Fmethod
              { mf_name = Id.of_string "clone";
                mf_tparams = [];
                mf_ret_type = self_ty;
                mf_params = [];
                mf_body = clone_body;
                mf_is_const = true;
                mf_is_static = false;
                mf_is_inline = false;
                mf_this_pos = 0;
                mf_no_pure = true;
                mf_is_noexcept = false; },
            VPublic, SAccessors )
        in
        let factory_name =
          Id.of_string (factory_name_of_ctor ~type_name:ind_type_name_str cname_str)
        in
        let factory_params =
          List.mapi (fun j ty ->
            let cpp_ty =
              erase_if_needed
                (convert_ml_type_to_cpp_type (empty_env ()) vars ty) in
            let fid = List.nth field_ids j in
            (fid, cpp_ty)
          ) tys_list
        in
        let factory_args =
          List.map (fun (param_name, cpp_ty) ->
            if is_trivially_copyable_type cpp_ty then CPPvar param_name
            else CPPmove (CPPvar param_name)
          ) factory_params
        in
        let factory_body = [Sreturn (Some (CPPbraced factory_args))] in
        let factory_field =
          ( Ffundef (factory_name, Tmod (TMstatic, self_ty), factory_params, factory_body),
            VPublic, SCreators )
        in
        let method_fields = List.map (gen_single_method name vars) method_candidates in
        let all_flat_fields = flat_fields @ [clone_field; factory_field] @ method_fields in
        Dstruct
          { ds_ref = name;
            ds_fields = all_flat_fields;
            ds_tparams = templates;
            ds_constraint = None;
            ds_needs_shared_from_this = false; }
      end else

      let _ = ind_type_name_str in (* suppress unused warning if non-flat path also needs it *)

      (* 1. Constructor alternative structs (simple, just fields, no make) *)
      let constructor_structs =
        Array.to_list
          (Array.mapi
             (fun i tys_list ->
               let c = cnames.(i) in
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               (* Fields: convert types, using self_ty for recursive
                  references *)
               let ctor_struct_name = Id.to_string cname in
               let ctor_consarg_names =
                 if i < Array.length consarg_names then consarg_names.(i)
                 else []
               in
               let n_fields = List.length tys_list in
               let field_ids =
                 compute_and_register_field_names ctor_struct_name
                   (augment_with_args_renaming c ctor_consarg_names)
                   ctor_consarg_names n_fields
               in
               let fields =
                 List.mapi
                   (fun j ty ->
                     let cpp_ty =
                       convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
                         vars
                         ty
                     in
                     (* Wrap fields that contain a nested self-reference in
                        their type arguments (e.g. list(tree(A)) inside tree).
                        The cycle is broken at the field level using a bare
                        (no-ns) type so the outer shared_ptr provides pointer
                        indirection without extra inner shared_ptrs for elements.
                        E.g. option(chain) → shared_ptr<optional<chain>>,
                             list(tree)   → shared_ptr<List<tree>>.
                        The body sees *a0 at the bare type directly with no
                        element-wise conversion needed. *)
                     let cpp_ty =
                       if ml_type_has_nested_self_ref ~ind_ref:name ty then
                         let bare_cpp_ty =
                           convert_ml_type_to_cpp_type
                             (empty_env ())
                             vars
                             ty
                         in
                         if is_coinductive then Tshared_ptr bare_cpp_ty
                         else Tshared_ptr bare_cpp_ty
                       else cpp_ty
                     in
                     let cpp_ty =
                       if vars = [] then
                         match cpp_ty with
                         | Tshared_ptr _ ->
                           tvar_erase_type cpp_ty
                         | _ when has_unnamed_tvar cpp_ty -> Tany
                         | _ -> cpp_ty
                       else cpp_ty
                     in
                     let field_name = List.nth field_ids j in
                     (Fvar (field_name, cpp_ty), VPublic, SNoTag) )
                   tys_list
               in
               (Fnested_struct (cname, fields), VPublic, STypes) )
             tys )
      in

      (* 2. variant_t type alias - use simple Id-based refs that match nested struct names *)
      (* Note: nested structs inherit template params from parent, so don't add <A> to them *)
      let variant_ty =
        Tvariant
          (Array.to_list
             (Array.mapi
                (fun i c ->
                  let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                  (* Use Tid for local nested struct types - no template args
                     since they inherit *)
                  Tid (cname_id, []) )
                cnames ) )
      in
      (* Collision detection: internal names must not equal the enclosing type name *)
      let type_name_str = Common.pp_global_name Type name in
      let escape_if_clashes base =
        if String.equal base type_name_str then base ^ "_" else base
      in
      let variant_alias_name = escape_if_clashes "variant_t" in
      let variant_using =
        (Fnested_using (Id.of_string variant_alias_name, variant_ty), VPublic, STypes)
      in
      let element_using = [] in

      (* 3. Private variant member: v_ for inductive, lazy_v_ for coinductive *)
      let variant_member_name =
        escape_if_clashes
          (if Table.std_lib () = "BDE" then
             (if is_coinductive then "d_lazyV_" else "d_v_")
           else
             (if is_coinductive then "lazy_v_" else "v_"))
      in
      let variant_alias_id = Id.of_string variant_alias_name in
      let variant_alias_ty = Tid (variant_alias_id, []) in
      let vmn_id = Id.of_string variant_member_name in
      let variant_member_ty =
        if is_coinductive then
          Tid
            ( Id.of_string_soft "crane::lazy",
              [variant_alias_ty] )
        else
          variant_alias_ty
      in
      let variant_member =
        ( Fvar (Id.of_string variant_member_name, variant_member_ty),
          VPrivate,
          SData )
      in

      (* 4. Public explicit constructors for each alternative.
         Public so that std::make_shared / std::make_unique can construct
         instances directly (single allocation). *)
      (* Note: nested struct types don't need template args - they inherit from parent *)
      let public_ctors =
        Array.to_list
          (Array.mapi
             (fun i c ->
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               let param_name = Id.of_string "_v" in
               let param_ty = Tid (cname, []) in
               if is_coinductive then
                 (* For coinductive:
                    d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) *)
                 let init_expr =
                   CPPfun_call
                     ( CPPvar (Id.of_string_soft ("crane::lazy<" ^ variant_alias_name ^ ">")),
                       [
                         CPPfun_call
                           ( CPPvar variant_alias_id,
                             [CPPmove (CPPvar param_name)] );
                       ] )
                 in
                 let init_list = [(vmn_id, init_expr)] in
                 ( Fconstructor ([(param_name, param_ty)], init_list, true, false),
                   VPublic,
                   SCreators )
               else
                 (* For inductive: d_v_(std::move(_v)) when the constructor
                    struct has non-trivial fields (shared_ptr etc.).  For
                    trivially-copyable structs (e.g., empty nullary constructors
                    like O, Nil, Leaf), skip std::move — it has no effect and
                    triggers performance-move-const-arg. *)
                 let has_nontrivial_fields =
                   List.exists (fun ty -> not (isTdummy ty)) tys.(i)
                 in
                 let init_v =
                   if has_nontrivial_fields then CPPmove (CPPvar param_name)
                   else CPPvar param_name
                 in
                 let init_list =
                   [(vmn_id, init_v)]
                 in
                 ( Fconstructor ([(param_name, param_ty)], init_list, true, false),
                   VPublic,
                   SCreators ) )
             cnames )
      in

      (* Default constructor for value-type inductives.  The variant
         default-constructs to its first alternative (e.g. Nil), which lets
         loopify declare [T _result{};] for stack-based iteration. *)
      let default_ctor =
        if not is_coinductive then
          [( Fconstructor ([], [], false, false),
             VPublic,
             SCreators )]
        else
          []
      in

      (** Iterative destructor preventing stack overflow from deeply recursive
          [shared_ptr] chains.  Drains recursive fields into an explicit stack,
          only entering nodes with [use_count() == 1] (sole ownership).

          Self-recursive types use [shared_ptr<Self>] directly on the stack.
          Mutually recursive types use [std::any] to hold different [shared_ptr]
          types.  Returns [[]] for non-recursive or coinductive types. *)
      let iterative_destructor =
        if is_coinductive then []
        else
          (** Check whether ML type [t] is a reference to [ref_name] applied to
              the same type variables [ref_vars] (i.e., a direct recursive or
              mutual recursive occurrence). *)
          let rec is_ref_to ref_name ref_vars = function
            | Miniml.Tglob (r, args, _) ->
              globref_equal r ref_name
              && List.length args = List.length ref_vars
              && List.for_all
                   (fun (j, arg) ->
                     match arg with
                     | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} ->
                       k = j + 1
                     | _ -> false)
                   (List.mapi (fun j a -> (j, a)) args)
            | Miniml.Tmeta {contents = Some t} -> is_ref_to ref_name ref_vars t
            | _ -> false
          in
          let is_direct_self_ref t = is_ref_to name vars t in
          let is_mutual_ref ty =
            List.exists
              (fun (pname, _, _, _) -> is_ref_to pname vars ty)
              mutual_partners
          in
          let rec classify_ml_self_ref = function
            | ml_ty when is_direct_self_ref ml_ty -> `Direct
            | Miniml.Tglob (g, [arg], _)
              when is_list_global g && is_direct_self_ref arg ->
              `List g
            | Miniml.Tmeta {contents = Some t} -> classify_ml_self_ref t
            | _ -> `None
          in
          let has_mutual =
            Array.exists (fun tys_list ->
              List.exists is_mutual_ref tys_list) tys
          in
          (* Shared identifiers used across the destructor body *)
          let _stack_id = Id.of_string "_stack" in
          let _alt_id = Id.of_string "_alt" in
          let _v_id = Id.of_string "_v" in
          let _cur_id = Id.of_string "_cur" in
          let _sp_id = Id.of_string "_sp" in
          let _pv_id = Id.of_string "_pv" in
          let variant_t_ty = Tid (Id.of_string "variant_t", []) in
          let self_ty = Tglob (name, ty_vars, []) in
          let render_q_destr ty =
            let skip g = GlobRef.CanOrd.equal g name in
            render_cpp_type_for_raw_template (qualify_inductives ~skip ty)
          in
          (** Build drain statements for classified fields.  [Direct] fields get
              a simple [push_back(std::move(field))].  [List g] fields with a
              custom mapping (e.g. std::deque) iterate elements onto the stack. *)
          let mk_classified_field_stmts classified_fields =
            List.concat_map (fun (field_id, cls) ->
              let fe = CPParrow (CPPvar _alt_id, field_id) in
              match cls with
              | `Direct ->
                [Sif_then (fe,
                  [Sexpr (CPPdot_method_call (
                     CPPvar _stack_id,
                     Id.of_string "push_back",
                     [CPPmove fe]))])]
              | `List list_g ->
                let ss = render_q_destr self_ty in
                let fes =
                  Id.to_string _alt_id ^ "->"
                  ^ Id.to_string field_id
                in
                (* This iterative drain replaces the naive recursive destructor,
                   so cleanup of a deep deque-backed recursive value no longer
                   overflows the call stack (the primary CWE-674 mitigation;
                   regression: tests/regression/deque_deep_tree_stackoverflow).
                   Residual tradeoff (CWE-400): the drain heap-allocates one
                   [make_shared] wrapper per element, so under extreme memory
                   pressure an allocation inside this (noexcept) destructor can
                   still terminate the process.  Eliminating that would require
                   an allocation-free intrusive worklist -- a larger redesign
                   deferred here; bounded call-stack depth is the property that
                   matters for the adversarial-depth attack. *)
                if Table.is_custom list_g then
                  [Sif_then (
                    CPPbinop ("&&", fe,
                      CPPbinop ("==",
                        CPPraw (fes ^ ".use_count()"),
                        CPPint 1)),
                    [ Sraw ("for (auto& _elem : *" ^ fes ^ ") {");
                      Sexpr (CPPdot_method_call (
                        CPPvar _stack_id,
                        Id.of_string "push_back",
                        [CPPraw (
                           "std::make_shared<" ^ ss
                           ^ ">(std::move(_elem))")]));
                      Sraw "}";
                      Sraw (fes ^ ".reset();") ])]
                else
                  let ls = render_q_destr (Tglob (list_g, [self_ty], [])) in
                  let (_nil_s, cons_s) = list_ctor_struct_names list_g in
                  let elem_field =
                    Id.to_string
                      (Common.lookup_ctor_field_name cons_s 0)
                  in
                  let tail_field =
                    Id.to_string
                      (Common.lookup_ctor_field_name cons_s 1)
                  in
                  [Sif_then (
                    CPPbinop ("&&", fe,
                      CPPbinop ("==",
                        CPPraw (fes ^ ".use_count()"),
                        CPPint 1)),
                    [ Sraw ("auto* _lp = " ^ fes ^ ".get();");
                      Swhile (
                        CPPraw (
                          "std::holds_alternative<typename "
                          ^ ls ^ "::" ^ cons_s
                          ^ ">(_lp->v())"),
                        [ Sraw (
                            "auto& _lc = std::get<typename "
                            ^ ls ^ "::" ^ cons_s
                            ^ ">(_lp->v_mut());");
                          Sexpr (CPPdot_method_call (
                            CPPvar _stack_id,
                            Id.of_string "push_back",
                            [CPPraw (
                               "std::make_shared<" ^ ss
                               ^ ">(std::move(_lc." ^ elem_field ^ "))")]));
                          Sraw (
                            "if (_lc." ^ tail_field ^ ") {"
                            ^ " _lp = _lc." ^ tail_field ^ ".get();"
                            ^ " } else { break; }") ]);
                      Sraw (fes ^ ".reset();") ])]
              | _ -> []) classified_fields
          in
          (** For each constructor, classify recursive fields and build an
              [Sif_decl] that uses [get_if] to test the variant alternative
              and drain recursive fields onto the stack.  Returns [Some stmt]
              for constructors with recursive fields, [None] otherwise.

              @param parent_ty    type to qualify the constructor in [get_if]
              @param ctor_opt     [Some ctor_id] for qualified access
                                  ([typename Parent::Ctor]), [None] for bare
              @param variant_var  identifier of the variant to test *)
          let mk_ctor_drain parent_ty ctor_opt variant_var i tys_list cnames_arr =
            let classified_fields =
              List.filter_map
                (fun (j, ty) ->
                  let cls = classify_ml_self_ref ty in
                  let is_mutual = is_mutual_ref ty in
                  if cls <> `None || is_mutual then
                    let cname_str =
                      ctor_struct_name_of_ref ~fallback_idx:i cnames_arr.(i)
                    in
                    let field_id =
                      Common.lookup_ctor_field_name cname_str j
                    in
                    let effective_cls =
                      if is_mutual then `Direct else cls
                    in
                    match effective_cls with
                    | `Direct -> Some (field_id, `Direct)
                    | `List g -> Some (field_id, `List g)
                    | _ -> None
                  else None)
                (List.mapi (fun j ty -> (j, ty)) tys_list)
            in
            match classified_fields with
            | [] -> None
            | _ ->
              let ctor_id =
                ctor_struct_id_of_ref ~fallback_idx:i cnames_arr.(i)
              in
              let ctor_arg = match ctor_opt with
                | None -> (Tid (ctor_id, []), None)
                | Some _ -> (parent_ty, Some ctor_id)
              in
              Some (Sif_decl (
                _alt_id, Tptr Tauto,
                CPPstd_get_if (fst ctor_arg, snd ctor_arg,
                  CPPunop ("&", CPPvar variant_var)),
                mk_classified_field_stmts classified_fields,
                []))
          in
          let drain_stmts =
            Array.to_list
              (Array.mapi
                 (fun i tys_list ->
                   mk_ctor_drain self_ty None _v_id i tys_list cnames)
                 tys)
            |> List.filter_map Fun.id
          in
          match drain_stmts with
          | [] -> []
          | _ when not has_mutual ->
            (* Self-recursive only: stack holds shared_ptr<Self> directly *)
            let stack_elem_ty = Tshared_ptr self_ty in
            let stack_ty =
              Tid_external (Id.of_string_soft "std::vector", [stack_elem_ty])
            in
            let _drain_id = Id.of_string "_drain" in
            let drain_lambda =
              CPPlambda (
                [(Tref variant_t_ty, Some _v_id)],
                None, drain_stmts, false)
            in
            let body =
              [ Sasgn (_stack_id, Some stack_ty,
                  CPPbraced []);
                Sasgn (_drain_id, Some Tauto, drain_lambda);
                Sexpr (CPPfun_call (CPPvar _drain_id,
                  [CPPfun_call (CPPvar (Id.of_string "v_mut"), [])]));
                Swhile (
                  CPPunop ("!",
                    CPPdot_method_call (CPPvar _stack_id,
                      Id.of_string "empty", [])),
                  [ Sasgn (_cur_id, Some Tauto,
                      CPPmove (CPPdot_method_call (CPPvar _stack_id,
                        Id.of_string "back", [])));
                    Sexpr (CPPdot_method_call (CPPvar _stack_id,
                      Id.of_string "pop_back", []));
                    Sif_then (
                      CPPbinop ("==",
                        CPPdot_method_call (CPPvar _cur_id,
                          Id.of_string "use_count", []),
                        CPPint 1),
                      [Sexpr (CPPfun_call (CPPvar _drain_id,
                        [CPPmethod_call (CPPvar _cur_id,
                          Id.of_string "v_mut", [])]))])
                  ])
              ]
            in
            [(Fdestructor body, VPublic, SManipulators)]
          | _ ->
            (* Mutual recursion: stack holds std::any to accommodate
               shared_ptrs of different types in the mutual group *)
            let stack_ty =
              Tid_external (Id.of_string_soft "std::vector", [Tany])
            in
            let _drain_self_id = Id.of_string "_drain_self" in
            let drain_self_lambda =
              CPPlambda (
                [(Tref variant_t_ty, Some _v_id)],
                None, drain_stmts, false)
            in
            (** Build the per-partner drain logic used inside the while loop.
                For each partner type, generates an [Sif_decl] that casts the
                [std::any] stack entry to [shared_ptr<Partner>], then drains
                the partner's recursive fields into the shared stack. *)
            let gen_partner_branch (pname, pcnames, ptys, _) =
              let partner_ty = Tglob (pname, ty_vars, []) in
              let partner_drains =
                Array.to_list
                  (Array.mapi
                     (fun pi ptys_list ->
                       mk_ctor_drain partner_ty (Some ()) _pv_id
                         pi ptys_list pcnames)
                     ptys)
                |> List.filter_map Fun.id
              in
              (partner_ty, partner_drains)
            in
            let partner_branches =
              List.map gen_partner_branch mutual_partners
            in
            (* Build the chained if/else-if for any_cast branches in the loop.
               Self branch: any_cast<shared_ptr<Self>>, call _drain_self.
               Partner branches: any_cast<shared_ptr<Partner>>, inline drain. *)
            let deref_sp = CPPderef (CPPvar _sp_id) in
            let sp_alive_and_unique =
              CPPbinop ("&&", deref_sp,
                CPPbinop ("==",
                  CPPdot_method_call (deref_sp,
                    Id.of_string "use_count", []),
                  CPPint 1))
            in
            let self_branch_body =
              [Sif_then (sp_alive_and_unique,
                [Sexpr (CPPfun_call (CPPvar _drain_self_id,
                  [CPPmethod_call (deref_sp,
                    Id.of_string "v_mut", [])]))])]
            in
            let rec build_if_chain branches =
              match branches with
              | [] -> []
              | (partner_ty, partner_drains) :: rest ->
                let inner = build_if_chain rest in
                let partner_body =
                  [Sif_then (sp_alive_and_unique,
                    Sasgn (_pv_id, Some (Tref Tauto),
                      CPPmethod_call (deref_sp,
                        Id.of_string "v_mut", []))
                    :: partner_drains)]
                in
                [Sif_decl (_sp_id, Tptr Tauto,
                  CPPany_cast (Tshared_ptr partner_ty,
                    CPPunop ("&", CPPvar _cur_id)),
                  partner_body, inner)]
            in
            let loop_body_stmts =
              [Sif_decl (_sp_id, Tptr Tauto,
                CPPany_cast (Tshared_ptr self_ty,
                  CPPunop ("&", CPPvar _cur_id)),
                self_branch_body,
                build_if_chain partner_branches)]
            in
            let body =
              [ Sasgn (_stack_id, Some stack_ty, CPPbraced []);
                Sasgn (_drain_self_id, Some Tauto, drain_self_lambda);
                Sexpr (CPPfun_call (CPPvar _drain_self_id,
                  [CPPfun_call (CPPvar (Id.of_string "v_mut"), [])]));
                Swhile (
                  CPPunop ("!",
                    CPPdot_method_call (CPPvar _stack_id,
                      Id.of_string "empty", [])),
                  Sasgn (_cur_id, Some Tauto,
                    CPPmove (CPPdot_method_call (CPPvar _stack_id,
                      Id.of_string "back", [])))
                  :: Sexpr (CPPdot_method_call (CPPvar _stack_id,
                       Id.of_string "pop_back", []))
                  :: loop_body_stmts)
              ]
            in
            [(Fdestructor body, VPublic, SManipulators)]
      in

      (* For coinductive types, add public constructor accepting
         std::function<variant_t()> (public so make_shared can access it) *)
      let lazy_ctor =
        if is_coinductive then
          let param_name = Id.of_string "_thunk" in
          let param_ty = Tfun ([], variant_alias_ty) in
          let init_expr =
            CPPfun_call
              ( CPPvar (Id.of_string_soft ("crane::lazy<" ^ variant_alias_name ^ ">")),
                [CPPmove (CPPvar param_name)] )
          in
          let init_list = [(vmn_id, init_expr)] in
          [
            ( Fconstructor ([(param_name, param_ty)], init_list, true, false),
              VPublic,
              SCreators );
          ]
        else
          []
      in

      (* 5. Static factory methods.  Each constructor gets one factory
         method as a direct static member of the struct, returning by value.

         Factory names are the lowercase of the constructor struct name
         (e.g., Cons → cons).  If this collides with a C++ keyword or the
         type's own name, the factory falls back to PascalCase with trailing
         underscore (e.g., Char → Char_).  See {!factory_name_of_ctor}.

         Move semantics: All parameters use the "sink parameter" idiom
         (passed by value, std::move'd into the struct initializer).
         Non-coinductive recursive fields take the inner type by value and
         are wrapped in make_shared internally; coinductive fields take a
         [const shared_ptr<T>&]. *)
      let ind_type_name = Common.pp_global_name Type name in

      let mk_factory_methods ret_ty wrap_expr i tys_list =
        let c = cnames.(i) in
        let cname = ctor_struct_name_of_ref ~fallback_idx:i c in
        let fname =
          factory_name_of_ctor ~type_name:ind_type_name cname
        in
        let factory_name = Id.of_string fname in
        (* Convert ML types both as public API types and constructor storage
           types.  Public APIs remain value-shaped (empty ns); storage uses
           [name] in ns so non-coinductive recursive occurrences are
           [shared_ptr]-wrapped. *)
        let cpp_tys =
          List.mapi
            (fun j ty ->
              let storage_ty =
                convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
                  vars
                  ty
              in
              let api_ty =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  vars
                  ty
              in
              let storage_ty =
                if ml_type_has_nested_self_ref ~ind_ref:name ty then
                  (* Use bare (no-ns) type so factory param and storage are
                     consistent: shared_ptr<optional<chain>> not
                     shared_ptr<optional<shared_ptr<chain>>>. *)
                  if is_coinductive then Tshared_ptr api_ty
                  else Tshared_ptr api_ty
                else storage_ty
              in
              let storage_ty =
                if vars = [] then
                  match storage_ty with
                  | Tshared_ptr _ ->
                    tvar_erase_type storage_ty
                  | _ when has_unnamed_tvar storage_ty -> Tany
                  | _ -> storage_ty
                else storage_ty
              in
              let api_ty =
                if vars = [] then
                  match api_ty with
                  | Tshared_ptr _ ->
                    tvar_erase_type api_ty
                  | _ when has_unnamed_tvar api_ty -> Tany
                  | _ -> api_ty
                else api_ty
              in
              (j, storage_ty, api_ty) )
            tys_list
        in
        (* Derive factory parameter name from the registered field name.
           Factory params use the bare binder name (e.g. [left]) rather than
           the prefixed field name (e.g. [d_left]), since they are function
           parameters, not struct members.  Falls back to the full field id
           if stripping the [d_] prefix fails. *)
        let param_name_of j =
          let field_id = lookup_ctor_field_name cname j in
          let s = Id.to_string field_id in
          if String.length s > 2 && s.[0] = 'd' && s.[1] = '_' then
            Id.of_string (String.sub s 2 (String.length s - 2))
          else field_id
        in
        (* For owned recursive fields in value-type inductives, factory
           params take the inner value by value (sink parameter) so callers
           can move in.  Coinductive shared_ptr fields stay as const ref. *)
        let params =
          List.map
            (fun (j, storage_ty, api_ty) ->
              let param_ty =
                match storage_ty with
                | Tshared_ptr _ ->
                  if is_coinductive then Tref (Tmod (TMconst, api_ty))
                  else api_ty
                | _ -> api_ty
              in
              (param_name_of j, param_ty) )
            cpp_tys
        in
        let ctor_args =
          List.map
            (fun (j, storage_ty, api_ty) ->
              let var = CPPvar (param_name_of j) in
              match storage_ty with
              | Tfun (storage_args, storage_ret) -> begin
                match api_ty with
                | Tfun (api_args, api_ret) when List.length storage_args = List.length api_args
                  && storage_ty <> api_ty ->
                  let lambda_params =
                    List.mapi
                      (fun k storage_arg ->
                        (storage_arg, Some (Id.of_string ("x" ^ string_of_int k)))
                      )
                      storage_args
                  in
                  let call_args =
                    List.mapi
                      (fun k (_storage_arg, api_arg) ->
                        let arg_var =
                          CPPvar (Id.of_string ("x" ^ string_of_int k))
                        in
                        if _storage_arg = api_arg then
                          arg_var
                        else
                          gen_type_conversion_expr
                            ~src_ty:_storage_arg ~dst_ty:api_arg
                            arg_var )
                      (List.combine storage_args api_args)
                  in
                  let call = CPPfun_call (var, List.rev call_args) in
                  let ret =
                    if storage_ret = api_ret then
                      call
                    else
                      gen_type_conversion_expr
                        ~src_ty:api_ret ~dst_ty:storage_ret
                        call
                  in
                  CPPlambda
                    ( List.rev lambda_params,
                      None,
                      [Sreturn (Some ret)],
                      true )
                | _ when storage_ty = api_ty -> CPPmove var
                | _ ->
                  gen_type_conversion_expr
                    ~src_ty:api_ty ~dst_ty:storage_ty var
              end
              | Tshared_ptr inner ->
                let arg = if is_coinductive then var else CPPmove var in
                let converted =
                  if inner = api_ty then arg
                  else gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:inner arg
                in
                CPPfun_call (CPPmk_shared inner, [converted])
              | _ when storage_ty = api_ty ->
                if is_trivially_copyable_type api_ty then var
                else CPPmove var
              | _ ->
                gen_type_conversion_expr
                  ~src_ty:api_ty ~dst_ty:storage_ty var )
            cpp_tys
        in
        let ctor_struct =
          CPPstruct_id (Id.of_string cname, [], ctor_args)
        in
        let body = [Sreturn (Some (wrap_expr ctor_struct))] in
        let primary =
          ( Ffundef (factory_name, Tmod (TMstatic, ret_ty), params, body),
            VPublic,
            SCreators )
        in
        [primary]
      in
      let factory_methods =
        List.flatten
          (Array.to_list
             (Array.mapi
                (mk_factory_methods self_ty
                   (* Wrap constructor struct in parent type constructor:
                      O{} → Nat(O{}) — needed because constructors are
                      explicit. Use CPPglob with the inductive ref so
                      the printer emits the correct name (handles both
                      top-level and module-nested inductives). *)
                   (fun s -> CPPfun_call (mk_cppglob name [], [s])) )
                tys ) )
      in

      (* For coinductive types, add lazy_ factory method. lazy_ accepts
         std::function<T()> and adapts it to std::function<variant_t()>
         for the lazy constructor.  Returns T (value type). *)
      let lazy_factory =
        if is_coinductive then
          let lazy_name = Id.of_string "lazy_" in
          let thunk_param_ty = Tfun ([], self_ty) in
          let params = [(Id.of_string "thunk", thunk_param_ty)] in
          let adapter_lambda =
            CPPlambda
              ( [],
                Some variant_alias_ty,
                [
                  Sasgn
                    ( Id.of_string "_tmp",
                      Some self_ty,
                      CPPfun_call (CPPvar (Id.of_string "thunk"), []) );
                  Sreturn
                    (Some
                       (CPPfun_call
                          ( CPPmember
                              ( CPPvar (Id.of_string "_tmp"),
                                Id.of_string "v" ),
                            [] ) ) );
                ],
                true )
          in
          let thunk_arg =
            CPPfun_call
              ( CPPvar (Id.of_string_soft ("std::function<" ^ variant_alias_name ^ "()>")),
                [adapter_lambda] )
          in
          let ctor_expr =
            CPPfun_call (mk_cppglob name ty_vars, [thunk_arg])
          in
          let body = [Sreturn (Some ctor_expr)] in
          [
            ( Ffundef (lazy_name, Tmod (TMstatic, self_ty), params, body),
              VPublic,
              SCreators );
          ]
        else
          []
      in

      let value_copy_clone_methods =
        if is_coinductive then
          []
        else
          let converting_ctor =
            let all_fields_empty =
              Array.for_all (fun tys_list -> tys_list = []) tys
            in
            if vars = [] || all_fields_empty then []
            else
              let render_ty ty =
                render_cpp_type_for_raw_template
                  ~no_custom_inductives:(Refset'.singleton name)
                  (qualify_inductives
                     ~skip:(fun g -> GlobRef.CanOrd.equal g name)
                     ty)
              in
              let n_vars = List.length vars in
              let u_var_names =
                List.mapi
                  (fun i _ ->
                    Id.of_string
                      (if n_vars = 1 then "_U"
                       else "_U" ^ string_of_int i))
                  vars
              in
              let u_tys =
                List.mapi (fun i x -> Tvar (i, Some x)) u_var_names
              in
              let source_ty = Tglob (name, u_tys, []) in
              let source_type_s = render_ty source_ty in
              let n_ctors = Array.length cnames in
              let other_id = Id.of_string "_other" in
              let vmn_id = Id.of_string variant_member_name in
              let gen_branch i tys_list =
                let c = cnames.(i) in
                let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                let ctor_struct_name =
                  ctor_struct_name_of_ref ~fallback_idx:i c
                in
                let source_ctor_ty = Tvar (0, Some cname_id) in
                let field_info =
                  List.mapi
                    (fun j ty ->
                      let field_id =
                        lookup_ctor_field_name ctor_struct_name j
                      in
                      let make_field_ty var_names =
                        let bare_ty =
                          convert_ml_type_to_cpp_type (empty_env ())
                            var_names ty
                        in
                        let storage_ty =
                          convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name) var_names ty
                        in
                        if ml_type_has_nested_self_ref ~ind_ref:name ty then
                          if is_coinductive then Tshared_ptr bare_ty
                          else Tshared_ptr bare_ty
                        else storage_ty
                      in
                      let src_fty = make_field_ty u_var_names in
                      let dst_fty = make_field_ty vars in
                      (field_id, src_fty, dst_fty))
                    tys_list
                in
                let converted =
                  List.map
                    (fun (field_id, src_fty, dst_fty) ->
                      gen_type_conversion_expr
                        ~skip:(fun g -> GlobRef.CanOrd.equal g name)
                        ~src_ty:src_fty ~dst_ty:dst_fty
                        (CPPvar field_id))
                    field_info
                in
                (source_ctor_ty, cname_id, field_info, converted)
              in
              let branches =
                List.init n_ctors (fun i -> gen_branch i tys.(i))
              in
              (* Build body statements for each branch *)
              let make_branch_body cname_id field_info converted =
                match field_info with
                | [] ->
                  [Sassign_expr
                     ( CPParrow (CPPthis, vmn_id),
                       CPPstruct_id (cname_id, [], []) )]
                | _ ->
                  let bindings =
                    String.concat ", "
                      (List.map
                         (fun (id, _, _) -> Id.to_string id)
                         field_info)
                  in
                  let source_ctor_s =
                    "typename " ^ source_type_s ^ "::"
                    ^ Id.to_string cname_id
                  in
                  [Sraw (
                     "const auto& [" ^ bindings
                     ^ "] = std::get<" ^ source_ctor_s
                     ^ ">(" ^ "_other.v()" ^ ");");
                   Sassign_expr
                     ( CPParrow (CPPthis, vmn_id),
                       CPPstruct_id (cname_id, [], converted) )]
              in
              let body =
                if n_ctors = 1 then
                  let source_ctor_ty, cname_id, field_info, converted =
                    List.hd branches
                  in
                  make_branch_body cname_id field_info converted
                else
                  (* Build if/else if/else chain *)
                  let other_v =
                    CPPdot_method_call (CPPvar other_id,
                                       Id.of_string "v", [])
                  in
                  let rec build_if_chain = function
                    | [] -> CErrors.anomaly (Pp.str "iterative_destructor: empty constructor list")
                    | [(_, cname_id, field_info, converted)] ->
                      (* Last branch: no guard *)
                      make_branch_body cname_id field_info converted
                    | (_source_ctor_ty, cname_id, field_info, converted)
                      :: rest ->
                      let guard =
                        CPPfun_call
                          ( CPPstd_holds_alternative
                              (source_ty, Some cname_id),
                            [other_v] )
                      in
                      let body =
                        make_branch_body cname_id field_info converted
                      in
                      [Sif (guard, body, build_if_chain rest)]
                  in
                  build_if_chain branches
              in
              let tparams =
                List.map
                  (fun u -> (TTtypename, u))
                  u_var_names
              in
              let ctor_params =
                [(other_id,
                  Tref (Tmod (TMconst, source_ty)))]
              in
              [(Ftemplate_ctor (tparams, true, ctor_params, body),
                VPublic, SCreators)]
          in
          converting_ctor
      in

      (* Add public accessor for v_ to enable pattern matching from outside *)
      let v_accessor =
        if is_coinductive then
          (* For coinductive: const variant_t& v() const { return
             lazy_v_.force(); } *)
          ( Fmethod
              {
                mf_name = Id.of_string "v";
                mf_tparams = [];
                mf_ret_type =
                  Tmod (TMconst, Tref variant_alias_ty);
                mf_params = [];
                mf_body =
                  [
                    Sreturn
                      (Some
                         (CPPfun_call
                            ( CPPmember
                                ( CPPvar vmn_id,
                                  Id.of_string "force" ),
                              [] ) ) );
                  ];
                mf_is_const = true;
                mf_is_static = false;
                mf_is_inline = false;
                mf_this_pos = 0;
                mf_no_pure = false;
                  mf_is_noexcept = false;
              },
            VPublic,
            SAccessors )
        else (* For inductive: const variant_t& v() const { return v_; } *)
          ( Fmethod
              {
                mf_name = Id.of_string "v";
                mf_tparams = [];
                mf_ret_type =
                  Tmod (TMconst, Tref variant_alias_ty);
                mf_params = [];
                mf_body = [Sreturn (Some (CPPvar vmn_id))];
                mf_is_const = true;
                mf_is_static = false;
                mf_is_inline = false;
                mf_this_pos = 0;
                mf_no_pure = false;
                  mf_is_noexcept = false;
              },
            VPublic,
            SAccessors )
      in

      (* Add mutable accessor for reuse optimization (Phase 3). For
         non-coinductive types: variant_t& v_mut() { return v_; } Not generated
         for coinductive types (lazy evaluation complicates reuse). *)
      let v_mut_accessor =
        if is_coinductive then
          []
        else
          [
            ( Fmethod
                {
                  mf_name = Id.of_string "v_mut";
                  mf_tparams = [];
                  mf_ret_type = Tref variant_alias_ty;
                  mf_params = [];
                  mf_body = [Sreturn (Some (CPPvar vmn_id))];
                  mf_is_const = false;
                  mf_is_static = false;
                  mf_is_inline = true;
                  mf_this_pos = 0;
                  mf_no_pure = true;
                  mf_is_noexcept = false;
                },
              VPublic,
              SManipulators );
          ]
      in

      (* 6. Generate methods from method candidates using shared helper *)
      let method_fields =
        List.map (gen_single_method name vars) method_candidates
      in

      (* Detect if any method contains shared_from_this (i.e., returns 'this').
         If so, the struct needs to inherit from
         std::enable_shared_from_this. *)
      let needs_shared_from_this =
        List.exists
          (fun (fld, _vis, _tag) ->
            match fld with
            | Fmethod {mf_body; _} ->
              List.exists stmt_has_shared_from_this mf_body
            | _ -> false )
          method_fields
      in

      (* Categorize user methods: const methods are ACCESSORS, non-const are
         MANIPULATORS *)
      let method_fields =
        List.map
          (fun (fld, vis, _tag) ->
            match fld with
            | Fmethod {mf_is_const = true; _} -> (fld, vis, SAccessors)
            | Fmethod _ -> (fld, vis, SManipulators)
            | _ -> (fld, vis, SNoTag) )
          method_fields
      in
      (* Split methods into manipulators and accessors *)
      let method_manipulators =
        List.filter (fun (_, _, tag) -> tag = SManipulators) method_fields
      in
      let method_accessors =
        List.filter (fun (_, _, tag) -> tag <> SManipulators) method_fields
      in

      (* BDE field ordering: public: constructor structs, variant_using (TYPES)
         private: variant_member (DATA)
         public: public_ctors + lazy_ctor + factory methods (CREATORS),
         v_mut + manipulators (MANIPULATORS),
         v_accessor + const methods (ACCESSORS) *)
      let all_fields =
        constructor_structs
        @ [variant_using]
        @ element_using
        @ [variant_member]
        @ default_ctor
        @ public_ctors
        @ value_copy_clone_methods
        @ lazy_ctor
        @ factory_methods
        @ lazy_factory
        @ iterative_destructor
        @ v_mut_accessor
        @ method_manipulators
        @ [v_accessor]
        @ method_accessors
      in

      (* Just the struct itself - no extra namespace wrapper *)
      Dstruct
        {
          ds_ref = name;
          ds_fields = all_fields;
          ds_tparams = templates;
          ds_constraint = None;
          ds_needs_shared_from_this = needs_shared_from_this;
        }

(** Generate methods for eponymous records. Uses the shared gen_single_method
    helper for records where methods are generated directly on the module struct
    (which has record fields merged). name: the record's GlobRef (e.g., IndRef
    for CHT) vars: the type variables of the record (e.g., [K; V] for CHT<K, V>)
    method_candidates: list of (func_ref, body, type, this_position) tuples *)
let gen_record_methods (name : GlobRef.t) (vars : Id.t list) method_candidates =
  List.map (gen_single_method name vars) method_candidates
 
