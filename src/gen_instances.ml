(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type-class instances: the struct carrying an instance's methods, its
    template head, and the static assertion against the class's concept. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Util
open Translation_state
open Ml_type_util
open Translation
open Gen_context
open Gen_records

module IntSet = Escape.IntSet

(** An instance's type and body past its own parameters -- erased type
    binders and class dictionaries, an eta-reduced instance's included
    ({!Instance_methods.layers}) -- with the template parameters the
    dictionaries become and the binders stripped. *)
let instance_layers ty body =
  let {Instance_methods.inner_ty; inner_body; dictionaries; lam_params} = Instance_methods.layers ty body in
  (* A dictionary becomes a concept-constrained template parameter -- [PreCategory
     _tcI0] instead of [typename _tcI0] -- so the compiler enforces concept
     satisfaction.  Unary concepts are expressed inline as [Eq _tcI0];
     multi-parameter concepts like [Numeric<I, t_A>] carry their kept type
     args so a [requires C<_tcI0, T1>] clause can be emitted at the use site
     instead of silently degrading to an unconstrained [typename] (CWE-693 /
     CWE-345). *)
  let constraint_of = function
    | Miniml.Tglob _ as arg_ty -> Option.default TTtypename (concept_constraint_of_class_type arg_ty)
    | _ -> TTtypename
  in
  (inner_ty, inner_body, List.map (fun (id, arg_ty) -> (constraint_of arg_ty, id)) dictionaries, lam_params)


(** The concrete types the instance [name] -- [body] of type [ty] -- gives
    its class's promoted variables, which a call through the instance
    substitutes for them: none where its body builds no record of its class,
    or where it does not give them all. *)
let instance_promoted_types name body ty =
  let inner_ty, inner_body, _, lam_params = instance_layers ty body in
  match (inner_ty : ml_type) with
  | Tglob (class_ref, type_args, _) when Table.is_typeclass class_ref -> (
    match Instance_methods.record_body name class_ref inner_ty lam_params inner_body with
    | MLcons (cons_ty, _, _) ->
      let type_args = Instance_methods.record_type_args cons_ty type_args in
      let promoted_vars = class_promoted_vars class_ref in
      let promoted_concrete = class_promoted_concrete class_ref type_args in
      if List.length promoted_vars = List.length promoted_concrete && promoted_vars <> [] then
        List.map2
          (fun var_name (params, ml_ty) ->
            (* Call sites want a closed type; the alias template's own
               element parameters ([Tvar 1 ...] here) have no meaning
               outside the instance, so they are erased. *)
            ( var_name,
              Mlutil.type_subst_list (List.map (fun _ -> Miniml.Tunknown) params) ml_ty ) )
          promoted_vars promoted_concrete
      else []
    | _ -> [] )
  | _ -> []

(** Generate a C++ struct for a type class instance.
   Type class instances become structs with static methods.
   Example: Instance IntEq : Eq int := { eqb := Int.eqb }.
   becomes: struct IntEq { static bool eqb(int a, int b) { ... } };

   Returns: (struct_decl option, class_ref option, type_args)
   The class_ref and type_args are used to generate static_assert in cpp.ml *)
let gen_instance_struct ?(bodies = true) (name : GlobRef.t) (body : ml_ast) (ty : ml_type) :
    cpp_decl option * GlobRef.t option * cpp_type list =
  let instance_ref = name in
  (* Without bodies the methods are their heads alone: what planning reads
     ({!plan_instance_methods}), decided by the very code that generates
     them. *)
  let gen_stmts env k e = if bodies then gen_stmts env k e else [] in
  let inner_ty, inner_body, tc_temps, lam_params = instance_layers ty body in
  (* Collect type variables from the inner return type's type args. For
     parameterized instances like numOption : Numeric (option A), the return
     type is Tglob(Numeric, [option A], []) which contains Tvar for A. These
     need to become template typename parameters (T1, T2, etc.). *)
  let instance_tvars = Instance_methods.instance_tvars ty inner_ty in
  let tv_temps =
    List.mapi (fun i _ -> (TTtypename, tvar_id (i + 1))) instance_tvars
  in
  (* The declared parameters are dense -- the first one written is [T1] -- but
     the variables they stand for need not be.  [Monad_stateT] binds [m] before
     [S] and reaches [m] through its [Monad m] dictionary, so the carrier
     [stateT S m] writes [Tvar 2] alone and the instance declares one parameter
     for it.  A name list read positionally would then answer [T1] for [m] and
     nothing for [S].  Names are therefore placed at the index each variable
     actually has, with the gaps filled by a placeholder: a variable the
     instance binds and does not declare has no C++ spelling here, and the
     substitution that resolves it -- through the dictionary -- runs before
     anything reads this list. *)
  let tv_names_by_index =
    let named = List.mapi (fun i v -> (v, tvar_id (i + 1))) instance_tvars in
    List.init
      (List.fold_left max 0 instance_tvars)
      (fun k ->
        match List.assoc_opt (k + 1) named with
        | Some id -> id
        | None -> Id.of_string "_" )
  in
  (* Template params: typeclass params first, then type vars (matches gen_dfun
     convention) *)
  let template_params = tc_temps @ tv_temps in
  (* A promoted associated type named inside the instance's own field bodies is
     the associated type of one of its class-typed parameters, and resolves
     through that parameter -- [typename _tcI0::iptr] -- exactly as it does in
     the signature of a function taking the same parameter ({!gen_dfun} builds
     the same map from the same function).

     Without it the bodies are generated as the module-level constructor
     expressions they are for an unparameterised instance, where an unresolved
     promoted variable falls back to [std::any] because a module-level alias is
     all there is to name.  Here there is [_tcI0], and the declaration next to
     the body already uses it, so the fallback puts the two in disagreement
     inside one struct. *)
  let promoted_var_resolutions =
    List.concat_map
      (fun (tt, inst_id) ->
        match tt with
        | TTconcept (class_ref, _) ->
          promoted_resolutions class_ref (Tinstance (inst_id, class_ref))
        | _ -> [] )
      tc_temps
  in
  (* The promoted variables of this instance's class arguments, which were
     specialised away and reach C++ through nothing else -- see
     {!instance_arg_resolutions}.  They come second, so a variable the
     surviving parameters already resolve keeps that resolution. *)
  let specialised_arg_resolutions =
    instance_arg_resolutions
      ~own_instances:
        (List.filter_map
           (fun (tt, inst_id) ->
             match tt with
             | TTconcept (class_ref, _) -> Some (Tinstance (inst_id, class_ref))
             | _ -> None )
           tc_temps )
      name
  in
  (* The arguments the instance's [static_assert] spells.  They are the ones
     {!concept_constraint_of_class_type} gives every other use of the concept
     -- the class's kept arguments, then the promoted variables it mentions --
     and the mentioned ones are resolved against this instance rather than
     left bare, because bare at namespace scope is the file-scope
     [using ptr = std::any;] and not the instance standing beside it. *)
  let resolve_mentioned t =
    match t with
    | Tpromoted v -> (
      match
        List.find_opt (fun (v', _) -> Id.equal v v') (!tctx).promoted_var_map
      with
      | Some (_, r) -> r
      | None -> t )
    | t -> t
  in
  let concept_args class_ref args =
    List.map (convert_ml_type_to_cpp_type (empty_env ()) []) args
    @ List.map resolve_mentioned (mentioned_promoted_args class_ref)
  in
  with_promoted_var_map
    ( promoted_var_resolutions @ specialised_arg_resolutions
    @ (!tctx).promoted_var_map )
  @@ fun () ->
  (* The instance's own head spells the same mentioned variables in its
     parameters' constraints -- [requires PI<_tcI2, ptr>] -- and they resolve
     through the parameters beside them the same way: [ptr] is
     [typename _tcI1::ptr], not the file-scope [std::any]. *)
  let template_params = Minicpp.map_tparams resolve_mentioned template_params in
  (* Now inner_ty should be Tglob(class_ref, type_args, _) and inner_body should
     be MLcons(...) *)
  match inner_ty with
  | Tglob (class_ref, type_args, _) when Table.is_typeclass class_ref ->
    (* Get the type class fields (method names) and field types (from
       ind_packet) *)
    let fields = Table.record_field_bindings_of_type inner_ty in
    (* Promoted dependent records may have their constructor wrapped in
       MLmagic due to Tvar/Tglob mismatches during extraction unification. *)
    let inner_body = Instance_methods.record_body name class_ref inner_ty lam_params inner_body in
    ( match inner_body with
    | MLcons (cons_ty, _ctor_ref, method_bodies) ->
      (* For promoted dependent records, the definition type Tglob(Magma,[],[])
         has no type_args, but the MLcons type Tglob(Magma,[nat],[]) carries the
         concrete types extracted from the erased constructor args.  The
         constructor's type arguments are preferred because extraction unified
         them against the body, which the definition's type need not mention.
         But a position extraction {e erased} says less, not more, and the two
         disagree exactly there: [Instance showCarr {C : Carrier} : Show carr]
         reaches here as [Show carr] in its declared type and [Show _] in its
         constructor's, because a class field standing as a type is a
         projection the constructor's unification drops.  Take the better of
         the two at each position rather than one list whole. *)
      let type_args = Instance_methods.record_type_args cons_ty type_args in
      (* How many type variables the instance itself binds.  Not the number of
         template parameters it declares: a higher-kinded carrier ([Instance
         ... (M : Type -> Type)]) is a variable the instance's arguments name,
         but it becomes an associated type rather than a parameter.

         Nor is it what the carrier {e writes}.  [Monad_stateT] binds [S] and
         [m] and its carrier [stateT S m] names only [S]: the inner monad
         reaches the instance through the dictionary [Monad m], so it is in
         [ty] and nowhere in [type_args].  A method body still numbers its own
         quantifiers after it, so counting from the arguments alone leaves the
         body's [A] one slot too high -- and the two are then read as one
         method variable too many, which spends [_A0] on the inner monad and
         erases [A], the variable the name was for.  The instance's own type
         is where every variable it binds is visible. *)
      let instance_tvar_count = Instance_methods.tvar_count ~instance_tvars ty type_args in
      let inst = {Instance_methods.class_ref; type_args; tvar_count = instance_tvar_count} in
      (* The concrete types it gives its class's promoted variables, which
         call sites substitute, were planned before rendering
         ({!instance_promoted_types}). *)
      if Probe.checking () then begin
        let planned = Table.get_instance_promoted_types name in
        let generated = instance_promoted_types name body ty in
        if
          not
            (List.equal
               (fun (v, t) (v', t') -> Id.equal v v' && Mlutil.eq_ml_type t t')
               planned generated )
        then
          Probe.violation "instance promoted types"
            Pp.(str "the instance " ++ GlobRef.print name ++ str " gives its promoted variables other types than planned")
      end;
      (* Build the environment with lambda parameters for de Bruijn resolution.
         For parameterized instances, method bodies reference the outer lambda
         parameters (e.g., the typeclass dictionary) via MLrel indices. We push
         lam_params into the env so these references resolve correctly. *)
      let outer_binders, base_env = push_vars' (List.rev lam_params) (empty_env ()) in
      (* Collect type var names for convert_ml_type_to_cpp_type *)
      let type_var_names = tv_names_by_index in
      (* Set up type variable context for fixpoint lifting. Without this,
         fixpoints inside methods get lifted with wrong names and missing
         template parameters. *)
      let saved_decl_ref = !Table.current_decl_ref in
      Table.current_decl_ref := Some name;
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
            Common.id_of_global Term method_ref
          in
          let m = Instance_methods.prepare_method inst method_ref field_ml_ty field_body in
          let {Instance_methods.field_ml_ty; subst_args; subst_ty; n_method_tvars; declared_arity; body = field_body} = m in
          let method_args_and_ret () = Instance_methods.args_and_ret m in
          let orig_args_and_ret () = Instance_methods.declared_args_and_ret m in
          (* With the quantifier back, the method is a member template:
             [template <typename _A0> static Opt<_A0> mret(_A0)] rather than a
             signature erased to [std::any].  Its own type variables sit past
             the class's, which [type_subst_list] has just replaced. *)
          let method_tvars, type_var_names =
            match n_method_tvars with
            | 0 -> ([], type_var_names)
            | n ->
              let ipv = List.length (Table.get_ind_ip_vars class_ref) in
              let names = List.init n hkt_alias_param_name in
              let pad =
                List.init
                  (max 0 (max ipv instance_tvar_count
                          - List.length type_var_names))
                  (fun _ -> Id.of_string "_")
              in
              (names, type_var_names @ pad @ names)
          in
          set_current_type_vars type_var_names;
          let subst_promoted_tvars = Instance_methods.subst_promoted_tvars inst in
          (* The instance's own binders were extracted at the class's erased
             field types.  For a higher-kinded class the declared signature
             ([subst_ty]) knows better: it still names the element type. *)
          (* Each kept argument beside the class's own statement of it.  The
             substituted type is what to spell; the class's is what says at
             which arity, and the two questions have different answers as soon
             as substitution unfolds an alias into arrows.  [bind]'s callback
             is declared [A -> m B] -- one value arrow -- and the instance's
             [m] is [stateT S m0], whose body is itself an arrow, so the
             substituted parameter has two.  Flattened, that is a
             [std::function] of two arguments against a call site that hands
             it one.

             The class's list is taken by the same split as the substituted
             one, so the two align where they are the same length.  Where they
             are not -- substitution can erase a parameter the class declared,
             and the splits then consume different numbers of dummies -- no
             pairing is attempted and the arity is left unsaid.  A neighbour's
             arity is worse than none: it would respell a parameter that was
             right. *)
          let declared_arg_pairs =
            let subst_args = fst (method_args_and_ret ()) in
            let orig_args = fst (orig_args_and_ret ()) in
            if List.length subst_args = List.length orig_args then
              List.map2 (fun s o -> (s, Some o)) subst_args orig_args
            else List.map (fun s -> (s, None)) subst_args
          in
          let kept_arg_pairs =
            List.filter (fun (t, _) -> not (erased_by_extraction t))
              declared_arg_pairs
          in
          (* A class-typed binder keeps its slot here: it still stands as a
             lambda in the body, and dropping it would misalign the declared
             types against the binders they retype. *)
          let declared_arg_tys = Array.of_list (List.map fst kept_arg_pairs) in
          (* How much of the declaration a binder is given.

             A member template's binders are retyped outright: the body was
             extracted against the class's erased method type, where the
             method's own [forall A] has no witness at all, so its annotations
             are not a weaker statement of the declared type but a different
             one.

             Everywhere else the declaration only fills what the body left
             open.  It has to be offered at all -- a field type standing as a
             type in another class's method domain ([int_to_ptr : nat ->
             @prov P -> EOU ptr]) reaches the body erased, while the same
             [prov] in the codomain is spelled [typename _tcI0::prov] four
             lines up -- and it may not be taken whole, because the body's own
             annotation is the one its statements were generated against. *)
          let offer_declared have want =
            if method_tvars <> [] then want
            else
              Ml_type_util.refine_erased
                ~writable:(fun t ->
                  not
                    (Ml_type_util.has_unbound_tvar type_var_names
                       (convert_ml_type_to_cpp_type base_env type_var_names t)) )
                have want
          in
          let declared_arg_arities =
            Array.of_list
              (List.map
                 (fun (_, o) -> Option.map count_ml_value_arrows o)
                 kept_arg_pairs )
          in
          (* The parameter's C++ type at the arity its declaration was written
             at ([Declared_at]): the arrows substitution moved into the
             callable's parameter list go back where the signature had them. *)
          let param_cpp_ty n ml_ty =
            let ty = convert_ml_type_to_cpp_type base_env type_var_names ml_ty in
            match
              (if n < Array.length declared_arg_arities then
                 declared_arg_arities.(n)
               else None)
            with
            | Some k when k > 0 -> Minicpp.spell_arrows (Declared_at k) ty
            | _ -> ty
          in
          (* A class-typed argument is not a value in C++: the class is a
             concept, and the instance satisfying it is a type.  Such a binder
             becomes one of the method's own template parameters, which is
             where its uses ([pa::width()]) already look for it. *)
          let binders, inner_body =
            let params, inner_body = Instance_methods.params m in
            let _, binders =
              List.fold_left_map
                (fun n {Instance_methods.binder = id; binder_ty = ty; erased} ->
                  if erased then
                    (n, {mb_name = id_of_mlid id; mb_ml_ty = ty; mb_cpp_ty = Tany; mb_kind = `Erased})
                  else
                    let resolved_ty =
                      let have = subst_promoted_tvars ty in
                      if n < Array.length declared_arg_tys then offer_declared have declared_arg_tys.(n)
                      else have
                    in
                    ( n + 1,
                      {
                        mb_name = id_of_mlid id;
                        mb_ml_ty = resolved_ty;
                        mb_cpp_ty = param_cpp_ty n resolved_ty;
                        mb_kind = (if Table.is_typeclass_type resolved_ty then `Instance else `Value);
                      } ) )
                0 params
            in
            (binders, inner_body)
          in
          (* Determine return type: if type_subst resolved everything, use the
             substituted type. Otherwise, infer from the lambda binders. *)
          let method_ret_ty =
            let ret = snd (method_args_and_ret ()) in
            (* A variable the substitution put there -- [B := A] for
               [Instance : Conv (wrap A) A] -- is one of the instance's own
               parameters, not a class variable the instance left open. *)
            let substituted =
              match snd (orig_args_and_ret ()) with
              | Miniml.Tvar (_, j) -> j <= List.length subst_args
              | _ -> true
            in
            match ret with
            | (Miniml.Tvar (_, _)) when method_tvars <> [] || substituted ->
              (* The method is a member template, or the variable is the
                 instance's, so a bare type variable in the return type is
                 already meaningful -- no need to guess it from the last
                 binder. *)
              convert_ml_type_to_cpp_type base_env type_var_names ret
            | (Miniml.Tvar (_, _)) when binders <> [] ->
              (* Unsubstituted Tvar — infer from the last lambda binder's type.
                 For op : A -> A -> A with body MLlam(x, nat, MLlam(y, nat,
                 ...)), the return type is the same as the parameter type
                 (nat). *)
              let last_param_ty = (List.hd (List.rev binders)).mb_ml_ty in
              convert_ml_type_to_cpp_type
                base_env
                type_var_names
                last_param_ty
            | Miniml.Tvar (_, _) ->
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
          (* The body is generated in the method's return-type context, as a
             top-level function's body is: an expression whose C++ type is the
             erased [std::any] -- a call to a higher-rank callback, say -- is
             cast back to the concrete type the method declares. *)
          (* Names for the class-typed arguments when the body does not bind
             them itself.  Numbered as an instance parameter is, since that is
             what they are. *)
          let n_tc_args_names =
            List.mapi
              (fun i _ -> tc_instance_id i)
              (List.filter
                 (fun ty -> parameter_role ty = Dictionary)
                 (fst (method_args_and_ret ())) )
          in
          let cpp_params, ret_ty, body_stmts, tc_tparams =
            with_cpp_return_type (Some method_ret_ty) @@ fun () ->
            if bodies then begin_body ~owner:name ();
            if List.for_all (fun b -> b.mb_kind = `Erased) binders then
              (* No lambdas the accessor can take its parameters from -- either
                 a function reference that needs eta-expansion, or a
                 non-function value field.  An erased binder is no parameter,
                 so a body that opens with nothing else is this case too. *)
              ( match Instance_methods.eta_call m inner_body with
              | None ->
                (* Non-function field (like m_id : carrier) — generate as a
                   static value with a nullary accessor method. *)
                let stmts =
                  gen_stmts base_env (fun x -> Sreturn (Some x)) inner_body
                in
                ([], method_ret_ty, stmts, [])
              | Some (eta_params, call_expr) ->
                (* Function reference — eta-expand. *)
                let params =
                  List.map
                    (fun (name, arg_ty) ->
                      (* A parameter is a declaration position: writing the
                         slot down as [std::any] is what makes the value
                         boxed, so a [Topaque] here becomes known-boxed. *)
                      let cpp_ty =
                        materialise_opaque
                          (convert_ml_type_to_cpp_type
                             base_env
                             type_var_names
                             arg_ty)
                      in
                      (name, arg_ty, cpp_ty) )
                    eta_params
                in
                (* Look up body function's types to detect mismatches from
                   inlined constants (e.g. Ref => "%t0" makes Ref A -> std::any
                   but refToIxNat expects RefNat).  Use the concrete types for
                   the env so method dispatch works, then prepend any_cast
                   bindings for params whose signature type is std::any. *)
                let body_arg_types =
                  (* A body defined inside a Section is already applied to the
                     section's (erased) variables, so the reference is under an
                     application of dummies rather than bare. *)
                  let rec body_ref = function
                    | MLglob {callee = r; _} -> Some r
                    | MLapp (f, args)
                      when List.for_all
                             (function MLdummy _ -> true | _ -> false) args ->
                      body_ref f
                    | MLmagic (_, e) -> body_ref e
                    | _ -> None
                  in
                  match body_ref inner_body with
                  | Some r -> (
                    try
                      let bty = Table.find_type r in
                      let bargs, _ = get_args_and_ret [] bty in
                      let bargs = List.filter (fun t ->
                        not (erased_by_extraction t)
                        && not (Table.is_typeclass_type t)) bargs in
                      if List.length bargs = List.length params then
                        Some bargs
                      else None
                    with Not_found -> None )
                  | None -> None
                in
                let cast_info =
                  List.filter_map (fun (i, (name, _ml_ty, sig_cpp)) ->
                    match body_arg_types with
                    | Some bargs ->
                      let body_ty = List.nth bargs i in
                      let body_cpp = convert_ml_type_to_cpp_type
                        base_env type_var_names body_ty in
                      if is_boxed_type sig_cpp && not (prints_as_any body_cpp)
                      then
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
                  with_method_env_types ~outer:outer_binders env renamed_eta (fun () ->
                    gen_stmts env (fun x -> Sreturn (Some x)) call_expr )
                in
                let stmts =
                  List.fold_left (fun acc (name, _body_ty, body_cpp) ->
                    let param_name =
                      Id.of_string ("_p_" ^ Id.to_string name) in
                    Sasgn (name, Declare body_cpp,
                           Cpp_erasure.unbox body_cpp (CPPvar param_name))
                    :: acc
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
                (* The eta path applied the class-typed arguments to
                   [MLdummy], so nothing in the body names them; the template
                   parameters are still declared, because the concept probe
                   and every call site spell the same list. *)
                (cpp_params, method_ret_ty, stmts, n_tc_args_names) )
            else
              (* Normal case: we have lambdas.  push_vars' lowercases
                 and uniquifies names for the de Bruijn environment;
                 sync cpp_params so the method signature matches. *)
              let renamed_ml, env =
                push_vars'
                  (List.rev_map (fun b -> (b.mb_name, b.mb_ml_ty)) binders)
                  base_env
              in
              let binders =
                List.map2
                  (fun (new_name, _) b -> {b with mb_name = new_name})
                  (List.rev renamed_ml)
                  binders
              in
              (* A class-typed binder leaves the value parameter list and
                 joins the template one, under the name the body knows it
                 by. *)
              let cpp_params =
                List.filter_map
                  (fun b ->
                    if b.mb_kind = `Value then
                      Some (b.mb_name, b.mb_cpp_ty)
                    else
                      None )
                  binders
              in
              let tc_tparams =
                List.filter_map
                  (fun b ->
                    if b.mb_kind = `Instance then Some b.mb_name else None )
                  binders
              in
              (* Record the instance-resolved parameter types: the ambient
                 environment still spells them with the class's type variable,
                 so call sites inside the body need this to tell a concrete
                 parameter (e.g. [Sz (nat -> nat)]'s [f]) from an erased one. *)
              let stmts =
                with_param_types (List.rev renamed_ml) @@ fun () ->
                (* The declared parameter types, so the body reads the
                   arities the signature was written at rather than
                   re-deriving them from ML types substitution has since
                   given extra arrows.  Same order as [renamed_ml]. *)
                with_method_env_types ~outer:outer_binders
                  ~cpp:(List.rev_map (fun b -> Some b.mb_cpp_ty) binders)
                  env renamed_ml
                  (fun () ->
                    gen_stmts env (fun x -> Sreturn (Some x)) inner_body )
              in
              (cpp_params, method_ret_ty, stmts, tc_tparams)
          in
          Some
            ( Fmethod
                {
                  mf_name = method_name;
                  (* The global the method is made from is the instance: it has
                     none of its own, so no call in its body names it, and a
                     call on a global that merely shares its label -- the
                     class's [fmap] at the inner instance, inside
                     [Functor_stateT]'s [fmap] -- is not a self-call. *)
                  mf_globref = Some instance_ref;
                  (* Undefaulted: every caller spells the arguments out --
                     the forwarding wrapper as [_tcI0::template ret<T2>(x)],
                     the concept probe at [std::any].  A default here would
                     let a call that fails to deduce silently fall back to
                     [std::any] instead of failing to compile. *)
                  (* The class-typed arguments follow the method's own type
                     variables: the concept probe supplies both lists, and it
                     reads the declared signature in the same order.  They are
                     left unconstrained, so that the probe can instantiate the
                     declaration at [std::any] without satisfying the class. *)
                  mf_tparams =
                    List.map
                      (fun p -> (TTtypename, p))
                      (method_tvars @ tc_tparams);
                  mf_ret_type = ret_ty;
                  mf_params = cpp_params;
                  mf_body = body_stmts;
                  mf_receiver = Static;
                  mf_is_inline = false;
                  mf_no_pure = false;
                  mf_is_noexcept = false;
                  mf_is_conversion = false;
                },
              VPublic,
              SNoTag )
      in
      let method_pairs =
        if List.length fields = List.length method_bodies then
          List.combine fields method_bodies
        else
          CErrors.anomaly
            (Pp.str
               (Printf.sprintf
                  "gen_decls: eponymous record has %d fields but its \
                   constructor has %d arguments"
                  (List.length fields)
                  (List.length method_bodies)))
      in
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
        | MLglob {callee = r; _} -> Tglob (r, [], [])
        | MLapp (MLglob {callee = r; _}, args) ->
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
            named_tvar name
          with Failure _ -> Tany )
        | MLmagic (_, e) -> ml_expr_to_cpp_type e
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
        if List.length fields = List.length method_bodies then
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
                  let field_id = Common.id_of_global Term field_ref in
                  let cpp_ty = ml_expr_to_cpp_type body in
                  if cpp_ty = Tany then None
                  else
                    Some
                      ( Fnested_using ([], field_id, cpp_ty),
                        VPublic,
                        SNoTag )
              | _ -> None )
            (List.combine fields method_bodies)
        else
          []
      in
      (* Restore type variable context *)
      Table.current_decl_ref := saved_decl_ref;
      clear_current_type_vars ();
      (* Compute promoted vars and generate using fields. Promoted vars are
         ip_vars entries beyond the real type parameter count (as determined by
         ip_sign Keep count, not tv_temps which reflects the instance's own type
         variables). They become `using field = ConcreteType;` in the struct. *)
      let promoted_vars = class_promoted_vars class_ref in
      (* The element parameters an alias template introduces are fresh type
         variables, so they have to be numbered past every variable the
         instance's arguments already use -- a carrier that is itself a
         variable ([Instance ... (M : Type -> Type)]) is one of those, and it
         is no template parameter, so [type_var_names] does not count it. *)
      let alias_tvar_base =
        List.fold_left
          (fun n t -> max n (Mlutil.type_maxvar t))
          (List.length type_var_names)
          type_args
      in
      let alias_tvar_names =
        type_var_names
        @ List.init
            (alias_tvar_base - List.length type_var_names)
            (fun _ -> Id.of_string "_")
      in
      let promoted_concrete_types =
        class_promoted_concrete ~tvar_base:alias_tvar_base class_ref type_args
      in
      (* Is [cpp_ty] a self-referential promoted-var reference (e.g.,
         [Tvar(_, Some "Obj")] where "Obj" is a promoted var)?  Such
         types are useless: [using Obj = Obj;] would just alias the
         enclosing scope, not the template parameter's type. *)
      let is_self_referential_promoted var_name cpp_ty =
        match cpp_ty with
        | Tpromoted id | Tvar (Tv_index (_, Some id) | Tv_named id) when Id.equal id var_name -> true
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
              (* Direct associated types only: the nested ones are added below,
                 keyed off the using names this produces. *)
              List.map
                (fun (var_name, arity) ->
                  (* A higher-kinded carrier forwards as an alias template,
                     since that is what the source instance declares. *)
                  let params = List.init arity hkt_alias_param_name in
                  let qualified_ty =
                    Tqualified (Tinstance (tc_name, class_ref_tc), var_name)
                  in
                  let qualified_ty =
                    if params = [] then qualified_ty
                    else
                      Tapply
                        ( qualified_ty,
                          List.map named_tvar params )
                  in
                  ( Fnested_using
                      ( List.map (fun p -> (TTtypename, p)) params,
                        var_name,
                        qualified_ty ),
                    VPublic,
                    SNoTag ) )
                (class_promoted_vars_arities class_ref_tc)
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
            | Fnested_using (_, id, _) -> Some id
            | _ -> None )
          tc_promoted_usings
      in
      (* Remove forwarded usings that are superseded by TC-promoted usings *)
      let forwarded_usings =
        List.filter
          (fun (f, _, _) ->
            match f with
            | Fnested_using (_, id, _) ->
              not (List.exists (Id.equal id) tc_promoted_names)
            | _ -> true )
          forwarded_usings
      in
      (* Generate [using VarName = ConcreteType;] for each promoted
         variable that has a known, non-self-referential concrete type.  Use
         zip-up-to-minimum so that partially-extractable Records still get
         declarations for the extractable promoted vars. *)
      let concrete_usings =
        let n =
          min (List.length promoted_vars) (List.length promoted_concrete_types)
        in
        List.init n (fun i ->
            let var_name = List.nth promoted_vars i in
            let alias_params, concrete_ml_ty =
              List.nth promoted_concrete_types i
            in
            let concrete_cpp_ty =
              convert_ml_type_to_cpp_type
                base_env
                (alias_tvar_names @ alias_params)
                concrete_ml_ty
            in
            (var_name, alias_params, concrete_cpp_ty) )
        |> List.filter_map (fun (var_name, alias_params, concrete_cpp_ty) ->
               if
                 List.exists (Id.equal var_name) tc_promoted_names
                 || is_self_referential_promoted var_name concrete_cpp_ty
               then
                 None
               else
                 Some
                   ( Fnested_using
                       ( List.map (fun p -> (TTtypename, p)) alias_params,
                         var_name,
                         concrete_cpp_ty ),
                     VPublic,
                     SNoTag ) )
      in
      (* The instance's own binding of a class field beats one forwarded from
         a parameter under the same name: [Monad_stateT] takes a [Monad] for
         the inner carrier, and forwarding its [m] would declare the inner
         carrier where the instance's own, [stateT S m], belongs.  The
         parameter's stays reachable as [_tcI0::m]. *)
      let forwarded_usings =
        let own =
          List.filter_map
            (fun (f, _, _) ->
              match f with Fnested_using (_, id, _) -> Some id | _ -> None )
            concrete_usings
        in
        List.filter
          (fun (f, _, _) ->
            match f with
            | Fnested_using (_, id, _) -> not (List.exists (Id.equal id) own)
            | _ -> true )
          forwarded_usings
      in
      (* Exclude promoted type args from the returned list (used for
         static_assert) *)
      let non_promoted_type_args =
        List.filteri (fun i _ -> is_class_tparam class_ref i) type_args
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
            match f with Fnested_using (_, id, _) -> Some id | _ -> None)
          direct_usings
      in
      let nested_promoted_usings =
        List.concat_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (_, using_name, _using_ty) ->
              (* Find this field's ML type in the typeclass definition *)
              let field_ml_ty =
                List.find_map
                  (fun (fld_opt, fml_ty) ->
                    match fld_opt with
                    | Some fld_ref ->
                      if Id.equal (Common.id_of_global Term fld_ref) using_name
                      then Some fml_ty
                      else None
                    | None -> None)
                  fields
              in
              ( match field_ml_ty with
              | Some (Miniml.Tglob (tc_ref, _, _))
                when Table.is_typeclass tc_ref ->
                let nested_promoted = class_promoted_vars tc_ref in
                List.filter_map
                  (fun v ->
                    if List.exists (Id.equal v) direct_names then None
                    else
                      Some
                        ( Fnested_using
                            ( [],
                              v,
                              Tqualified
                                (Tinstance (using_name, tc_ref), v) ),
                          VPublic,
                          SNoTag ))
                  nested_promoted
              | _ -> [] )
            | _ -> [])
          direct_usings
      in
      let all_usings = direct_usings @ nested_promoted_usings in
      if methods = [] && all_usings = [] then
        (None, Some class_ref, concept_args class_ref non_promoted_type_args)
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
        ( Some
            (apply_hkt_resolutions_decl (hkt_tvar_resolutions_of_type ~source_order:true ty) decl),
          Some class_ref,
          concept_args class_ref non_promoted_type_args )
    | MLglob {callee = other; _} ->
      (* The instance is nothing but another instance's name.  C++ has a
         spelling for exactly that, and without it the name is never
         declared at all. *)
      ( Some
          (Dusing
             { du_tparams = [];
               du_name = name;
               du_rhs = Some (Tglob (other, [], []));
               du_note = None } ),
        Some class_ref,
        concept_args class_ref type_args )
    | _ -> (None, Some class_ref, concept_args class_ref type_args) )
  | _ -> (None, None, [])

(** The callable plan of each method of the instance [name] -- [body] of
    type [ty] -- by the method's name, as generating its struct declares it,
    without generating a body: the struct's head is planned with the other
    callables, before anything is rendered.  [finish] is what becomes of the
    struct before it is written ({!Cpp_ind.instance_struct}). *)
let plan_instance_methods ~finish name body ty =
  let rec methods = function
    | Dstruct ds ->
      List.filter_map (function Fmethod mf, _, _ -> Some mf | _ -> None) ds.ds_fields
    | Dtemplate (_, _, d) -> methods d
    | _ -> []
  in
  match gen_instance_struct ~bodies:false name body ty with
  | Some decl, _, _ ->
    List.map (fun mf -> (mf.mf_name, Callable_abi.of_instance_method ~instance:name mf)) (methods (finish decl))
  | None, _, _ -> []

(** Check if a term is a type class instance (constructs a type class record) *)
let is_typeclass_instance (_body : ml_ast) (ty : ml_type) : bool =
  match ml_return_type ty with
  | Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false
