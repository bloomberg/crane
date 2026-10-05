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

(** Generate a C++ struct for a type class instance.
   Type class instances become structs with static methods.
   Example: Instance IntEq : Eq int := { eqb := Int.eqb }.
   becomes: struct IntEq { static bool eqb(int a, int b) { ... } };

   Returns: (struct_decl option, class_ref option, type_args)
   The class_ref and type_args are used to generate static_assert in cpp.ml *)
let gen_instance_struct (name : GlobRef.t) (body : ml_ast) (ty : ml_type) :
    cpp_decl option * GlobRef.t option * cpp_type list =
  let instance_ref = name in
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
            Option.default TTtypename
              (concept_constraint_of_class_type arg_ty)
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
  let dict_vars =
    let rec vars acc = function
      | Miniml.Tvar (_, i) | Miniml.Tapp (i, []) -> i :: acc
      | Miniml.Tapp (i, tys) -> List.fold_left vars (i :: acc) tys
      | Miniml.Tglob (_, tys, _) -> List.fold_left vars acc tys
      | Miniml.Tarr (a, b) -> vars (vars acc a) b
      | Miniml.Tmeta {contents = Some t} -> vars acc t
      | _ -> acc
    in
    List.fold_left
      (fun acc (_, t) -> if Table.is_typeclass_type t then vars acc t else acc)
      [] lam_params
  in
  let rec collect_ml_tvars acc = function
    | Miniml.Tvar (Schematic, i) ->
      if List.mem i acc then
        acc
      else
        i :: acc
    (* A family parameter -- [Functor (box E)] -- is written applied, and is
       one of the instance's variables all the same.  Not a carrier one of
       its dictionaries is about: [Monad m] reaches [m] through the
       dictionary, and the instance declares nothing for it. *)
    | Miniml.Tapp (i, tys) ->
      let acc =
        if List.mem i acc || List.mem i dict_vars then acc else i :: acc
      in
      List.fold_left collect_ml_tvars acc tys
    | Miniml.Tarr (t1, t2) -> collect_ml_tvars (collect_ml_tvars acc t1) t2
    | Miniml.Tglob (_, tys, _) -> List.fold_left collect_ml_tvars acc tys
    | Miniml.Tmeta {contents = Some t} -> collect_ml_tvars acc t
    | _ -> acc
  in
  let instance_tvars =
    match inner_ty with
    | Tglob (_, type_args, _) ->
      List.sort compare (List.fold_left collect_ml_tvars [] type_args)
    | _ -> []
  in
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
    (* Strip MLmagic wrapper if present — promoted dependent records may have
       their constructor wrapped in MLmagic due to Tvar/Tglob mismatches during
       extraction unification. *)
    let inner_body =
      match inner_body with
      | MLmagic (_, b) -> b
      | b -> b
    in
    ( match inner_body with
    | MLcons (cons_ty, _ctor_ref, method_bodies) ->
      (* For promoted dependent records, the definition type Tglob(Magma,[],[])
         has no type_args, but the MLcons type Tglob(Magma,[nat],[]) carries the
         concrete types extracted from the erased constructor args. *)
      (* The constructor's type arguments are preferred because extraction
         unified them against the body, which the definition's type need not
         mention.  But a position extraction {e erased} says less, not more,
         and the two disagree exactly there: [Instance showCarr {C : Carrier}
         : Show carr] reaches here as [Show carr] in its declared type and
         [Show _] in its constructor's, because a class field standing as a
         type is a projection the constructor's unification drops.  Take the
         better of the two at each position rather than one list whole. *)
      let type_args =
        let erased t =
          match resolve_tmeta t with
          | Miniml.Tunknown | Miniml.Tdummy _ -> true
          | _ -> false
        in
        match cons_ty with
        | Tglob (_, ta, _) when ta <> [] ->
          List.mapi
            (fun i t ->
              if not (erased t) then t
              else
                match List.nth_opt type_args i with
                | Some d when not (erased d) -> d
                | _ -> t )
            ta
        | _ -> type_args
      in
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
      let instance_tvar_count =
        List.fold_left
          (fun n t -> max n (Mlutil.type_maxvar t))
          (max (List.length tv_temps) (Mlutil.type_maxvar ty))
          type_args
      in
      (* Register promoted type bindings for this instance so that call sites
         (eta_fun) can substitute promoted Tvars with concrete types. E.g., for
         nat_magma : Magma, register [(carrier, nat)] so pick_op<nat_magma>
         eta-expansion uses unsigned int instead of std::any. *)
      let promoted_vars = class_promoted_vars class_ref in
      let promoted_concrete = class_promoted_concrete class_ref type_args in
      if
        List.length promoted_vars = List.length promoted_concrete
        && promoted_vars <> []
      then
        Table.add_instance_promoted_types
          name
          (List.map2
             (fun var_name (params, ml_ty) ->
               (* Call sites want a closed type; the alias template's own
                  element parameters ([Tvar 1 ...] here) have no meaning
                  outside the instance, so they are erased. *)
               ( var_name,
                 Mlutil.type_subst_list
                   (List.map (fun _ -> Miniml.Tunknown) params)
                   ml_ty ) )
             promoted_vars
             promoted_concrete );
      (* Build the environment with lambda parameters for de Bruijn resolution.
         For parameterized instances, method bodies reference the outer lambda
         parameters (e.g., the typeclass dictionary) via MLrel indices. We push
         lam_params into the env so these references resolve correctly. *)
      let base_env = snd (push_vars' (List.rev lam_params) (empty_env ())) in
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
          (* Strip MLmagic wrappers from the field body — promoted dependent
             records produce MLmagic due to Tvar/Tglob mismatches. *)
          let rec strip_magic = function
            | MLmagic (_, b) -> strip_magic b
            | b -> b
          in
          let field_body = strip_magic field_body in
          (* Substitute type class parameter with instance's type arg in the
             field type. This gives us the concrete return type (e.g., bool for
             eqb: A -> A -> bool). For promoted dependent records, type_args may
             be empty, leaving Tvars unsubstituted — we handle that below by
             using lambda binder types. *)
          let field_ml_ty =
            recover_method_quantifier class_ref method_ref field_ml_ty
          in
          (* The field numbers its own [forall A] right after the class's
             parameters, and the instance numbers its binders from one as
             well: [Monad_stateT]'s carrier [stateT S m] names the same
             variable the method's [A] does, so substituting the carrier in
             would spell [A] as the inner monad.  Move the method's variables
             above every instance binder first -- the positions the
             declaration binds them at anyway. *)
          let method_tvar_base =
            max (List.length (Table.get_ind_ip_vars class_ref))
              instance_tvar_count
          in
          let n_method_tvars = method_tvar_count class_ref field_ml_ty in
          let field_ml_ty =
            let nclass = List.length (Table.get_ind_ip_vars class_ref) in
            let own =
              List.sort compare
                (List.filter (fun i -> i > nclass)
                   (collect_tvars [] field_ml_ty))
            in
            let sub =
              List.mapi
                (fun k i ->
                  (i, Miniml.Tvar (Schematic, method_tvar_base + 1 + k)) )
                own
            in
            if List.for_all (fun (i, t) -> t = Miniml.Tvar (Schematic, i)) sub
            then field_ml_ty
            else subst_tvars_type sub field_ml_ty
          in
          (* Extraction eta-expands a type-constructor argument, so the
             carrier arrives as [option<_>] rather than the bare [option] the
             application needs; contract it before substituting.

             Unless the carrier is written with a [Tunknown] hole.  Then it is
             already the type-level lambda, the hole is its binder, and the
             binder may be written more than once: [stateT S m] arrives as
             [stateT(S, m _, _)], because the record's monad parameter is
             itself applied to the element.  Dropping the trailing argument
             keeps one occurrence and loses the other, and what comes out is a
             [stateT] short a template argument.  Applying a hole is filling
             it -- every occurrence at once -- which {!Mlutil.apply_ml_type}
             already does, so there is nothing to contract here. *)
          let subst_args =
            List.mapi
              (fun i t ->
                match t with
                | _ when Mlutil.type_has_hole t -> t
                | Miniml.Tglob (r, _ :: _, es)
                  when Table.is_hkt_param class_ref i ->
                  (* Only the eta-expanded arguments come off: a carrier that
                     arrived partially applied keeps the ones it fixed. *)
                  Miniml.Tglob
                    ( r,
                      hkt_carrier_fixed_args
                        (Table.get_ind_hkt_arity class_ref i)
                        t,
                      es )
                | Miniml.Tapp (j, _ :: _) when Table.is_hkt_param class_ref i
                  ->
                  (* Same contraction for a carrier that is a type variable:
                     what is left is the head the class applies. *)
                  ( match
                      hkt_carrier_fixed_args
                        (Table.get_ind_hkt_arity class_ref i)
                        t
                    with
                  | [] -> Miniml.Tvar (Schematic, j)
                  | fixed -> Miniml.Tapp (j, fixed) )
                | t -> t )
              (Ml_type_util.instance_type_args type_args)
          in
          let subst_ty = Mlutil.type_subst_list subst_args field_ml_ty in
          (* The concept requires the field at the arity the class declared it
             at, so an instance whose type argument is itself a function type
             ([Instance : D (nat -> nat)]) may not absorb the arrows that
             arrived with the substitution as further parameters: they belong
             to the value the accessor returns. *)
          let declared_arity = count_ml_value_arrows field_ml_ty in
          let split_at_declared_arity ty =
            let args, ret = get_args_and_ret [] ty in
            let rec split n acc = function
              | t :: rest
                when Mlutil.isTdummy t || Table.is_typeclass_type t ->
                split n (t :: acc) rest
              | t :: rest when n > 0 -> split (n - 1) (t :: acc) rest
              | surplus -> (List.rev acc, surplus)
            in
            let kept, surplus = split declared_arity [] args in
            ( kept,
              List.fold_right (fun a r -> Miniml.Tarr (a, r)) surplus ret )
          in
          let method_args_and_ret () = split_at_declared_arity subst_ty in
          let orig_args_and_ret () = split_at_declared_arity field_ml_ty in
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
          (* The declared signature numbers the method's own type variables
             after every parameter of the class, while the body -- extracted
             on its own -- numbers them after the instance's own binders, and
             need not have numbered them consecutively.  Read the body's
             quantifiers off the body and map them, in order, onto the
             positions [type_var_names] gives them; left alone the body would
             name [A] where the class carrier sits. *)
          let field_body =
            if n_method_tvars = 0 then field_body
            else
              let base = method_tvar_base in
              let body_tvars =
                let acc = ref [] in
                ignore
                  (Mlutil.ast_map_types
                     (fun t ->
                       acc := collect_tvars !acc t;
                       t )
                     field_body);
                List.sort compare
                  (List.filter (fun i -> i > instance_tvar_count) !acc)
              in
              let subst =
                List.mapi
                  (fun k i -> (i, Miniml.Tvar (Schematic, base + 1 + k)))
                  (safe_firstn n_method_tvars body_tvars)
                (* A body may name more variables than the field declares --
                   an inner monad the mode erases leaves one behind.  The
                   declaration binds what it declares and no more, so what is
                   left over is spelled the way any type the declaration
                   cannot name is: erased. *)
                @ List.filteri
                    (fun k _ -> k >= n_method_tvars)
                    (List.map (fun i -> (i, Miniml.Tunknown)) body_tvars)
              in
              if List.for_all (fun (i, t) -> t = Miniml.Tvar (Schematic, i)) subst
              then field_body
              else Mlutil.ast_map_types (subst_tvars_type subst) field_body
          in
          (* An instance method may have been eta-reduced below the arity its
             class field declares ([cmap A B f x := f x] extracts to
             [fun A B f => f]).  The concept requires the declared arity, so
             re-introduce the missing arguments.

             A body with no lambdas at all is left alone: the eta path in
             [gen_method] below handles the point-free case, and it also
             bridges a parameter the class declares at an erased type to the
             concrete type the named body expects. *)
          let rec nb_lams = function
            | MLlam (_, ty, rest) ->
              (if Mlutil.isTdummy ty then 0 else 1) + nb_lams rest
            | _ -> 0
          in
          (* A binder whose type extraction erased away ([token], a
             one-constructor inductive carrying no information) still occupies
             a parameter slot: the class declares the field at an arity every
             instance must meet, and the concept checks that arity.  Where the
             body's leading binders line up one-for-one with the declared
             arguments, the declaration's type wins over the body's erased
             annotation, so the parameter survives instead of being dropped as
             a proof binder would be. *)
          let field_body =
            let declared = fst (get_args_and_ret [] subst_ty) in
            let rec leading = function MLlam (_, _, r) -> 1 + leading r | _ -> 0 in
            if leading field_body <> List.length declared then field_body
            else
              let rec retype tys body =
                match (tys, body) with
                | ty :: rest, MLlam (id, bty, b) ->
                  let erased_value =
                    (* [Ktype] is an erased type abstraction -- the field's own
                       [forall A], which stands at no declared argument.  Any
                       other erased annotation is a value binder whose type
                       carried no information. *)
                    match bty with
                    | Miniml.Tdummy Miniml.Ktype -> false
                    | Miniml.Tdummy _ -> true
                    | _ -> false
                  in
                  let bty = if erased_value && not (Mlutil.isTdummy ty) then ty else bty in
                  MLlam (id, bty, retype rest b)
                | _ -> body
              in
              retype declared field_body
          in
          let field_body =
            if nb_lams field_body = 0 && Table.get_ind_hkt_params class_ref = []
            then field_body
            else
            let arg_types =
              List.filter
                (fun t ->
                  not (Table.is_typeclass_type t) && not (Mlutil.isTdummy t) )
                (fst (method_args_and_ret ()))
            in
            let missing =
              List.length arg_types - nb_lams field_body
            in
            if missing <= 0 then field_body
            else
              let missing_tys =
                List.filteri
                  (fun i _ -> i >= List.length arg_types - missing)
                  arg_types
              in
              let rec expand = function
                | MLlam (id, ty, rest) -> MLlam (id, ty, expand rest)
                | inner ->
                  let inner = Mlutil.ast_lift missing inner in
                  let args =
                    List.init missing (fun i -> MLrel (missing - i))
                  in
                  List.fold_left
                    (fun acc (i, ty) ->
                      MLlam (Id (Id.of_string ("a" ^ string_of_int i)), ty, acc) )
                    (MLapp (inner, args))
                    (List.rev (List.mapi (fun i t -> (i, t)) missing_tys))
              in
              expand field_body
          in
          (* Extract parameter names and types from the lambda. For promoted
             type vars (e.g., Tvar 3 for edge in Graph), substitute them with
             their concrete types from type_args. Only substitute Tvars beyond
             the ip_sign Keep count to avoid disturbing regular type variable
             references. *)
          let nb_sign_keeps = List.length tv_temps in
          let subst_promoted_tvars ty =
            if List.length type_args > nb_sign_keeps then
              let rec subst = function
                | Miniml.Tvar (Schematic, j)
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
          (* The body's embedded types still mention the class's promoted type
             variables ([list E] carries [Tvar 1], not [list nat]).  Resolve
             them exactly as the parameter and return types are resolved: left
             alone they would render as the concept's template parameter [T1],
             which is not in scope inside the instance struct. *)
          let field_body = Mlutil.ast_map_types subst_promoted_tvars field_body in
          (* The body was extracted at the class's erased field type, so its
             [MLcase] and [MLcons] annotations say [option _] where the
             declared signature says [option A].  Push the declared type back
             down, or the body would spell [Option<std::any>] against a value
             the signature typed [Option<_A0>]. *)
          let field_body = Mlutil.recover_erased_types subst_ty field_body in
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
            List.filter (fun (t, _) -> not (Mlutil.isTdummy t))
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
             at.  {!Minicpp.recurry_to} exists for exactly this: it puts the
             arrows substitution moved into the callable's parameter list back
             where the signature had them. *)
          let param_cpp_ty n ml_ty =
            let ty = convert_ml_type_to_cpp_type base_env type_var_names ml_ty in
            match
              (if n < Array.length declared_arg_arities then
                 declared_arg_arities.(n)
               else None)
            with
            | Some k when k > 0 -> Minicpp.recurry_to k ty
            | _ -> ty
          in
          (* A class-typed argument is not a value in C++: the class is a
             concept, and the instance satisfying it is a type.  Such a binder
             becomes one of the method's own template parameters, which is
             where its uses ([pa::width()]) already look for it. *)
          let rec extract_params n rem acc body =
            match body with
            (* Past the declared arity the remaining binders are the value's
               own, not the accessor's: they stay in the body, which the
               return type spells as a [std::function].  Checked before the
               erased case, since an erased binder past the arity is the
               value's too. *)
            | MLlam _ when n >= declared_arity -> (List.rev acc, body)
            | MLlam (id, ty, rest)
              when is_erasable_binder_ty ty
                   && (rem > declared_arity - n
                      || not (Mlutil.ast_occurs 1 rest)) ->
              (* An erased binder is no parameter, but it is still a binder:
                 dropping it would shift every de Bruijn index the body uses
                 to name the ones that remain.

                 A binder may only be dropped while binders are left to
                 spare, or while the body makes no use of it: extraction
                 sometimes annotates a value binder as erased ([ret := @Some]
                 extracts as [fun (_ : axiom) (x : dummy) => Some x]), and the
                 declared arity is what says how many of them the concept is
                 owed. *)
              extract_params
                n
                (rem - 1)
                ( {
                    mb_name = id_of_mlid id;
                    mb_ml_ty = ty;
                    mb_cpp_ty = Tany;
                    mb_kind = `Erased;
                  }
                :: acc )
                rest
            | MLlam (id, ty, rest) ->
              let resolved_ty =
                let have = subst_promoted_tvars ty in
                if n < Array.length declared_arg_tys then
                  offer_declared have declared_arg_tys.(n)
                else have
              in
              extract_params
                (n + 1)
                (rem - 1)
                ( {
                    mb_name = id_of_mlid id;
                    mb_ml_ty = resolved_ty;
                    mb_cpp_ty = param_cpp_ty n resolved_ty;
                    mb_kind =
                      ( if Table.is_typeclass_type resolved_ty then
                          `Instance
                        else
                          `Value );
                  }
                :: acc )
                rest
            | _ -> (List.rev acc, body)
          in
          let binders, inner_body =
            extract_params 0 (count_leading_lams field_body) [] field_body
          in
          (* Determine return type: if type_subst resolved everything, use the
             substituted type. Otherwise, infer from the lambda binders. *)
          let method_ret_ty =
            let ret = snd (method_args_and_ret ()) in
            match ret with
            | (Miniml.Tvar (_, _)) when method_tvars <> [] ->
              (* The method is a member template, so a bare type variable in
                 the return type is one of its own parameters and is already
                 meaningful -- no need to guess it from the last binder. *)
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
                 Table.is_typeclass_type
                 (fst (method_args_and_ret ())) )
          in
          let cpp_params, ret_ty, body_stmts, tc_tparams =
            with_cpp_return_type (Some method_ret_ty) @@ fun () ->
            begin_body ();
            if List.for_all (fun b -> b.mb_kind = `Erased) binders then
              (* No lambdas the accessor can take its parameters from -- either
                 a function reference that needs eta-expansion, or a
                 non-function value field.  An erased binder is no parameter,
                 so a body that opens with nothing else is this case too. *)
              let all_arg_types, _ret_type = method_args_and_ret () in
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
                ([], method_ret_ty, stmts, [])
              else
                (* Function reference — eta-expand.  Build C++ params only for
                   real args, but supply MLdummy for erased args in the ML
                   application so the body receives all expected arguments. *)
                let params =
                  List.mapi
                    (fun i arg_ty ->
                      let name = Id.of_string ("a" ^ string_of_int i) in
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
                  (* A body defined inside a Section is already applied to the
                     section's (erased) variables, so the reference is under an
                     application of dummies rather than bare. *)
                  let rec body_ref = function
                    | MLglob (r, _) -> Some r
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
                        not (Mlutil.isTdummy t)
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
                  with_method_env_types env renamed_eta (fun () ->
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
                (cpp_params, method_ret_ty, stmts, n_tc_args_names)
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
                with_method_env_types
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
            (apply_hkt_resolutions_decl (hkt_tvar_resolutions_of_type ty) decl),
          Some class_ref,
          concept_args class_ref non_promoted_type_args )
    | MLglob (other, _) ->
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

(** Check if a term is a type class instance (constructs a type class record) *)
let is_typeclass_instance (_body : ml_ast) (ty : ml_type) : bool =
  match ml_return_type ty with
  | Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false
