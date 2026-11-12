(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Whether a binder holds a box, planned from Core.  See
    [representation_plan.mli]. *)

open Miniml
open Minicpp
open Util
open Translation_state
open Ml_type_util
open Translation_support
open Translation_types

(* What decided a binder's C++ type, as {!Translation_state.binder_origin}
   says for the recorded one: the conversion of its ML type where it is
   bound, or the instantiation a match pinned down for a pattern binder. *)
type origin =
  | Binding
  | Pattern

(* The C++ type a binder in scope is planned to have, if one is: innermost
   first, beside the binder's ML type in {!Lexenv}. *)
type scope = {
  lex : Lexenv.t;
  planned : (cpp_type * origin) option list;
  kinds : binder_kind list;
}

(* Whether a planned type is a box. *)
let boxed = function
  | Some (Topaque, _) | None -> false
  | Some (t, _) -> resolves_to_any_type t

(* The type a binder of ML type [ty] is given where it is bound
   ({!Translation_types.assign_binder_types}): none where the conversion is
   [Topaque], a dummy, or fails. *)
let at_binding ty =
  match cpp_of_ml (Common.empty_env ()) ty with
  | t when t <> Topaque && not (is_cpp_dummy_type t) -> Some (t, Binding)
  | _ -> None
  | exception _ -> None

(* [scope] under the binders [ids], innermost first, each planned at the
   conversion of its ML type. *)
let push kind ids scope =
  { lex = Lexenv.push (List.map (fun (x, ty) -> {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = Lexenv.Value}) ids) scope.lex;
    planned = List.map (fun (_, ty) -> at_binding ty) ids @ scope.planned;
    kinds = List.map (fun _ -> kind) ids @ scope.kinds }

(* The domains a slot of C++ type [t] declares, where it declares a
   signature ({!Translation.gen_expr}'s [MLlam]). *)
let rec slot_domains t =
  match t with
  | Tnondeduced t | Tconst t | Tref (Lvalue, t) -> slot_domains t
  | Tfun (doms, _) -> Some doms
  | t -> (
    match unfold_cpp_typedef (Common.empty_env ()) t with
    | Tfun (doms, _) as f when f <> t -> Some doms
    | _ -> None )

(* What a lambda's parameters [ids] (innermost first, over [body]) are read
   at in its body ({!Translation.gen_expr}'s [MLlam]): each emitted one at
   the type it is declared ({!Translation_types.lambda_param_cpp_type}) and
   then assigned ({!Translation_types.lambda_param_assigned}) against the
   slot's domains [slot], in source order, where the slot declares a
   signature; one not emitted at the conversion of its ML type. *)
let push_parameters ?slot_ty ~ns ~tvars ~reified ~body ids scope =
  let scope = push Kparameter ids scope in
  let n = List.length ids in
  let slot = Option.bind slot_ty slot_domains in
  let emitted i ty = lambda_binder_emitted (Common.empty_env ()) ~expected_ty:slot_ty ~body ids i ty in
  let emitted_ids = List.filteri (fun i (_, ty) -> emitted i ty) ids in
  let n_emitted = List.length emitted_ids in
  let rank2_carrier =
    if slot = None && List.exists (fun (_, ty) -> Rank2.quantifies_erased_type ty) emitted_ids then
      Some Rank2.carrier_name
    else None
  in
  let declared =
    let k = ref 0 in
    List.mapi
      (fun i (x, ty) ->
        if not (emitted i ty) then at_binding ty
        else
          let j = !k in
          incr k;
          let slot_dom = Option.bind slot (fun doms -> List.nth_opt doms (n_emitted - 1 - j)) in
          match
            lambda_param_cpp_type (Common.empty_env ()) ~ns ~tvars ~rank2_carrier ~reified ~n_params:n ~body
              ~unused:(not (Mlutil.ast_occurs (i + 1) body))
              ~slot_dom
              (Mlutil.id_of_mlid x, ty, false)
          with
          | decl, _ -> (
            match strip_param_wrappers (lambda_param_assigned ~slot_dom ty decl) with
            | t when t <> Topaque && not (is_cpp_dummy_type t) -> Some (t, Binding)
            | _ -> None )
          | exception _ -> at_binding ty )
      ids
  in
  {scope with planned = declared @ List.filteri (fun i _ -> i >= n) scope.planned}

(* The type the binder at de Bruijn index [i] is planned to have. *)
let planned scope i = if i >= 1 then Option.flatten (List.nth_opt scope.planned (i - 1)) else None

(* {!Translation_types.scrutinee_binder}, with the binder's ML type read in
   [lex]. *)
let rec scrutinee_binder lex = function
  | MLrel (i, _) -> Some i
  | MLmagic (_, e) -> scrutinee_binder lex e
  | MLapp (h, _) when not (head_is_callable lex h) -> scrutinee_binder lex h
  | _ -> None

and head_is_callable lex h =
  match scrutinee_binder lex h with
  | Some i -> (
    let rec is_arrow = function Tmeta {contents = Some t} -> is_arrow t | Tarr _ -> true | _ -> false in
    match Lexenv.type_opt lex i with Some t -> is_arrow t | None -> true )
  | None -> true

(* {!Translation_types.record_binder_type}: a match pins [t] down for a
   binder planned [cur], unless a match already pinned a box there. *)
let pin cur t =
  match cur with
  | Some (t', Pattern) when t' <> Topaque && resolves_to_any_type t' -> cur
  | _ -> Some (t, Pattern)

let scrutinee_pinned scope scrut =
  match Option.bind (scrutinee_binder scope.lex scrut) (fun i -> List.nth_opt scope.planned (i - 1)) with
  | Some (Some (t, Pattern)) -> Some t
  | _ -> None

(* What the branch pins down about each field ({!Translation_types.populate_erased_field_env}):
   [planned], in field order, the types the binders are given where they are
   bound. *)
let pinned_fields scope ~typ ~scrut cname planned =
  let pins =
    pattern_field_pins ~scrut_pinned:(scrutinee_pinned scope scrut) ~cname ~typ ~env:(Common.empty_env ())
      ~n_fields:(List.length planned) ~non_erased_def_site_field_tys:(Ctor_fields.of_ctor cname).types
  in
  List.map2
    (fun p (stored_as_any, arg) ->
      let p = if stored_as_any then pin p Tany else p in
      match arg with Some t -> pin p t | None -> p )
    planned pins

(* The pattern variables [ids], in field order, of a branch matching [cname]
   in a match over [scrut] generated at [typ] ({!Translation.gen_cpp_case}). *)
let pattern_binders scope ~typ ~scrut cname ids =
  pinned_fields scope ~typ ~scrut cname (List.map (fun (_, ty) -> at_binding ty) (retype_dependent_params typ ids))

(* The same for a custom match annotated [ty] ({!Translation.gen_custom_cpp_case}):
   bound at the types {!Translation_types.custom_branch_binders} gives them,
   every field a box where the pair is read back as [pair<any, any>], then
   what the branch pins down, then every field a box that is not a list where
   the scrutinee is a boxed custom list. *)
let custom_pattern_binders scope ~(cs : custom_scrutinee) ~ty ~scrut cname ids =
  let fix_a_fired = cs.cs_pair_any_cast in
  let scrut_ml_typ =
    match Option.bind (scrutinee_binder scope.lex scrut) (Lexenv.type_opt scope.lex) with
    | Some t when not (ml_type_contains_erased t) -> t
    | _ -> ty
  in
  let bound =
    custom_branch_binders (Common.empty_env ()) ~fix_a_fired ~scrut_ml_typ ~ml_typ:ty cname
      (List.rev_map (fun (x, ty) -> (Mlutil.id_of_mlid x, ty)) ids)
  in
  let planned = List.rev_map (fun (_, ty) -> at_binding ty) bound in
  let planned = if fix_a_fired then List.map (fun p -> pin p Tany) planned else planned in
  let planned = pinned_fields scope ~typ:ty ~scrut cname planned in
  let elems_are_any =
    (cs.cs_mlmagic || cs.cs_magic)
    && match ty with Tglob (g, _ :: _, _) -> Ml_type_util.is_custom_list_global g | _ -> false
  in
  if elems_are_any then
    let def_tys = (Ctor_fields.of_ctor cname).types in
    List.mapi
      (fun i p ->
        match List.nth_opt def_tys i with
        | Some (Tglob (g, _, _)) when is_list_global g -> p
        | _ -> pin p Tany )
      planned
  else planned

(* Whether [a] projects a component out of a pair read from a binder that
   holds a box ({!Translation.eta_fun}'s pair-accessor case): the
   pair is recovered as [pair<any, any>], and its components are boxes. *)
let reads_boxed_component scope a =
  let is_pair_projection r =
    match Table.find_custom_opt r with
    | Some s -> ( match inline_shape_of_text s with Inline_pair_projection _ -> true | _ -> false )
    | None -> false
  in
  match a with
  | MLapp (MLglob {callee = r; _}, args) when Table.is_inline_custom r && is_pair_projection r -> (
    match List.filter (function MLdummy _ -> false | _ -> true) args with
    | arg :: _ -> (
      match strip_magic arg with
      | MLrel (i, _) -> (
        match Lexenv.type_opt scope.lex i with
        | Some t ->
          let t = resolve_tmeta t in
          is_erased_ml_type t || (try ml_erases_to_box (Common.empty_env ()) t with _ -> false)
        | None -> false )
      | _ -> false )
    | [] -> false )
  | _ -> false

let region ~outer body =
  let found = ref [] in
  let reads = ref [] in
  let promoted_active = (!tctx).promoted_var_map <> [] in
  let return = (!tctx).current_cpp_return_type in
  let type_vars = (!tctx).current_type_vars in
  let ns = (!tctx).method_self_ns in
  let reified = (!tctx).itree_mode = Reified in
  let parameters ?slot_ty ~body ids scope = push_parameters ?slot_ty ~ns ~tvars:type_vars ~reified ~body ids scope in
  let is_lambda a = match strip_magic a with MLlam _ -> true | _ -> false in
  (* A lambda stored in a constructor's field is written against [slot]
     where the constructor's lowering says what it is, otherwise against the
     field's type: its ML type converted. *)
  let rec walk_field_lambda ?slot scope field_ty lam =
    let ids, body = Mlutil.collect_lams lam in
    let slot_ty =
      match (slot, field_ty) with
      | Some s, _ -> s
      | None, Some t -> ( try Some (cpp_of_ml (Common.empty_env ()) t) with _ -> None )
      | None, None -> None
    in
    walk (parameters ?slot_ty ~body ids scope) body
  and walk scope = function
    (* A record projection ({!Translation.gen_expr}, {!Translation.gen_stmts}:
       after a custom match, before any other) declares its fields at the
       types they are bound at, pinned by nothing: as statements, with a
       dependent parameter's field retyped as erased; in an expression, not
       ([pr_bound_boxed]).  The body is planned at the statement form's. *)
    | MLcase (ty, scrut, ([|(ids, _, _, body)|] as branches), occ)
      when (not (Table.is_custom_match branches)) && Table.record_fields_of_type ty <> [] ->
      walk scope scrut;
      let bound = List.map (fun (_, t) -> at_binding t) ids in
      let retyped = List.map (fun (_, t) -> at_binding t) (retype_dependent_params ty ids) in
      List.iteri
        (fun i (r, b) ->
          found :=
            (Core_binder.Branch (occ, 0), i, {pr_boxed = boxed r; pr_bound_boxed = boxed b})
            :: !found )
        (List.combine retyped bound);
      let inner = push Kpattern (List.rev ids) scope in
      walk {inner with planned = List.rev retyped @ scope.planned} body
    | MLcase (ty, scrut, branches, occ) ->
      walk scope scrut;
      let var_type = Lexenv.type_opt scope.lex in
      let fields =
        if Table.is_custom_match branches then
          let cs =
            custom_match_scrutinee (Common.empty_env ()) ty scrut branches
              ~var_boxed:(fun i _ -> boxed (planned scope i)) ~var_type
          in
          custom_pattern_binders scope ~cs ~ty ~scrut
        else
          let typ =
            match_scrutinee_type (Common.empty_env ()) ty scrut branches ~var_type
              ~var_cpp_type:(fun i -> Option.map fst (planned scope i))
          in
          pattern_binders scope ~typ ~scrut
      in
      Array.iteri
        (fun bi (ids, _, pat, body) ->
          let inner = push Kpattern (List.rev ids) scope in
          let inner =
            match pat with
            | Pusual r | Pcons (r, _) when ids <> [] ->
              let field_planned = fields r ids in
              List.iteri
                (fun i p ->
                  let pr_bound_boxed =
                    match List.nth_opt ids i with Some (_, t) -> boxed (at_binding t) | None -> false
                  in
                  found :=
                    (Core_binder.Branch (occ, bi), i, {pr_boxed = boxed p; pr_bound_boxed})
                    :: !found )
                field_planned;
              {inner with planned = List.rev field_planned @ scope.planned}
            | _ -> inner
          in
          walk inner body )
        branches
    (* A lambda a custom constructor stores via [crane_erase_fn] is generated
       rewritten ({!Translation_types.erased_fn_lambda}): a custom match on its
       parameter reads it boxed.  Decided at the constructor's own drafted
       instantiation, which is lowering's wherever the destination states no
       more than the annotation. *)
    | MLcons (ty, r, args) when Table.is_custom r ->
      let env = Common.empty_env () in
      let field_tys =
        match Table.get_ctor_ip_types_opt r with
        | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
        | None -> []
      in
      let temps = ctor_draft_temps env ~promoted_active ~return ty in
      List.iteri
        (fun i e ->
          match strip_magic e with
          | MLlam _ when stores_erased_fn env r ~field_tys ~temps i e -> walk scope (erased_fn_lambda env e)
          | MLlam _ as lam ->
            (* The slot's own signature where it erased only its domain
               ({!Translation.gen_expr_custom_cons}'s [erased_fn_slot]). *)
            let erased_fn_slot =
              if ctor_arg_is_passthrough r i || not (ml_expr_is_function_value e) then None
              else
                match List.nth_opt field_tys i with
                | Some (Miniml.Tvar (_, j)) -> (
                  match Option.map tvar_erase_type (List.nth_opt temps (j - 1)) with
                  | Some t when partially_erased_fun_ty t -> Some t
                  | _ -> None )
                | _ -> None
            in
            walk_field_lambda ?slot:(Option.map (fun t -> Some t) erased_fn_slot) scope (List.nth_opt field_tys i) lam
          | _ -> walk scope e )
        args
    (* A record's field is written against the field's type at the record's
       arguments only where that type returns a function
       ({!Translation.gen_expr}'s record [expected_for_field]). *)
    | MLcons (ty, r, args) when List.exists is_lambda args && Table.record_fields_of_type ty <> [] ->
      let field_tys =
        match Table.get_ctor_ip_types_opt r with
        | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
        | None -> []
      in
      let env = Common.empty_env () in
      let rec codomain = function
        | Tconst t | Tref (_, t) -> codomain t
        | Tfun (_, cod) -> Some cod
        | t -> ( match unfold_cpp_typedef env t with Tfun _ as f when f <> t -> codomain f | _ -> None )
      in
      let slot ft =
        match (ft, ty) with
        | Miniml.Tvar _, _ -> None
        | _, Miniml.Tglob (_, tys, _) -> (
          match cpp_of_ml env (Mlutil.type_subst_list tys ft) with
          | ct -> (
            match codomain ct with
            | Some cod when Option.has_some (codomain cod) && (not (prints_as_any ct)) && names_only_scoped_tvars ct ->
              Some ct
            | _ -> None )
          | exception _ -> None )
        | _ -> None
      in
      List.iteri
        (fun i e ->
          match (strip_magic e, List.nth_opt field_tys i) with
          | (MLlam _ as lam), Some ft -> walk_field_lambda ~slot:(slot ft) scope (Some ft) lam
          | (MLlam _ as lam), None -> walk_field_lambda ~slot:None scope None lam
          | _ -> walk scope e )
        args
    | MLcons (_, r, args) when List.exists is_lambda args ->
      let field_tys =
        match Table.get_ctor_ip_types_opt r with
        | Some ft -> List.filter (fun t -> not (Mlutil.isTdummy t)) ft
        | None -> []
      in
      List.iteri
        (fun i e ->
          match strip_magic e with
          | MLlam _ as lam -> walk_field_lambda scope (List.nth_opt field_tys i) lam
          | _ -> walk scope e )
        args
    (* A lambda passed to a global is generated in the slot of the parameter
       it is passed at, its binders refined against that parameter's ML type
       ({!Translation_types.slot_refined_lambda}): the callee's declared
       type at the call's reading ({!Core_elaborate.instantiate}), where it
       erases nothing.  Read with no type the call's position states. *)
    | MLapp (MLglob use, args) when List.exists is_lambda args ->
      let call = Core_elaborate.elaborate_arguments ~lex:scope.lex use args in
      let inst =
        Core_elaborate.instantiate ~lex:scope.lex ~expected_ml:None ~stated_ml:None ~caller:(!tctx).body_owner
          ~scope:type_vars call
      in
      let leading = Elaborated_call.leading_params call in
      let param_ml_ty i =
        let param_index = Param_pos.of_regular ~leading i in
        let subst =
          if Table.is_inline_custom use.callee then Some (Param_pos.subst_at_declared param_index)
          else inst.subst_index_of_orig param_index
        in
        match subst with
        | Some j -> Param_pos.nth inst.params j
        | None -> (
          match Param_pos.nth inst.params_orig param_index with
          | Some t when not (erased_by_extraction t) -> Some t
          | _ -> None )
      in
      let regular_index a =
        let rec go i = function [] -> None | r :: rest -> if r == a then Some i else go (i + 1) rest in
        go 0 call.regular
      in
      List.iter
        (fun a ->
          match (strip_magic a, regular_index a) with
          | (MLlam _ as lam), Some i ->
            let expected_ml_ty =
              match param_ml_ty i with Some t when not (ml_type_contains_erased t) -> Some t | _ -> None
            in
            let ids, body = Mlutil.collect_lams lam in
            let ids, body = slot_refined_lambda (Common.empty_env ()) ~expected_ml_ty ids body in
            (* A callable the callee deduces is written against
               [const auto &] where the slot's domain is a box
               ({!Translation_calls.deduce_erased_domains}). *)
            let deduced = Callable_abi.deduces_callable use.callee (Param_pos.of_regular ~leading i) in
            let slot_ty =
              match param_ml_ty i with
              | Some t -> (
                match cpp_of_ml (Common.empty_env ()) t with
                | c when prints_as_any c -> None
                | c -> Some (if deduced then Translation_calls.deduce_erased_domains c else c)
                | exception _ -> None )
              | None -> None
            in
            walk (parameters ?slot_ty ~body ids scope) body
          | _ -> walk scope a )
        args
    (* A lambda passed to a local function is written against that
       function's declared domain at its position, where the binding site
       declared one with no erased position ({!Translation.eta_fun}'s
       [declared_dom]). *)
    | MLapp (((MLrel (h, _) | MLmagic (_, MLrel (h, _))) as f), args)
      when List.exists (function MLlam _ -> true | _ -> false) args ->
      walk scope f;
      let dom = match planned scope h with Some (Tfun (dom, _), _) -> dom | _ -> [] in
      List.iteri
        (fun k a ->
          match a with
          | MLlam _ as lam ->
            let slot_ty =
              match List.nth_opt dom k with
              | Some t when not (exists_cpp_type prints_as_any t) -> Some t
              | _ -> None
            in
            let ids, body = Mlutil.collect_lams lam in
            walk (parameters ?slot_ty ~body ids scope) body
          | _ -> walk scope a )
        (List.filter (function MLdummy _ -> false | _ -> true) args)
    | MLletin (x, ty, a, body, _) ->
      walk scope a;
      (* A component read out of a boxed pair is a box, however concrete its
         ML type looks; lowering binds it at a dummy type, with no C++ type
         recorded, so an accessor reading it again sees the erasure
         ({!Translation_types.stmts_yield_boxed}). *)
      let ty = if x <> Dummy && reads_boxed_component scope a then Tdummy Ktype else ty in
      walk (push Klet [(x, ty)] scope) body
    (* Any other lambda's binders at the types they are annotated with.
       Lowering also declares a parameter by the C++ slot the lambda fills --
       [const auto &], or [std::any] where the slot's domain is a box --
       which the check holds to the same answer for every pattern binder
       rooted at one, and counts for every read of one. *)
    | MLlam _ as e ->
      let ids, body = Mlutil.collect_lams e in
      walk (parameters ~body ids scope) body
    | MLfix (_, fs, defs, _, _) ->
      let scope = push Kfix (List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs)) scope in
      Array.iter (walk scope) defs
    (* A read: whatever its binder is planned. *)
    | MLrel (i, occ) ->
      let rd_kind = Option.default Kouter (List.nth_opt scope.kinds (i - 1)) in
      reads := (occ, {rd_boxed = boxed (planned scope i); rd_kind}) :: !reads
    | e -> Mlutil.ast_iter (walk scope) e
  in
  let depth = Lexenv.depth outer in
  let outer_planned = List.init depth (fun i -> Option.bind (Lexenv.type_opt outer (i + 1)) at_binding) in
  let scope = {lex = outer; planned = outer_planned; kinds = List.init depth (fun _ -> Kouter)} in
  (* A lambda the region returns is written against the region's return
     type. *)
  ( match (strip_magic body, return) with
  | (MLlam _ as e), Some t when slot_domains t <> None ->
    let ids, body = Mlutil.collect_lams e in
    walk (parameters ~slot_ty:t ~body ids scope) body
  | _ -> walk scope body );
  (!found, List.rev !reads)

let check ?(as_bound = false) ~site ~field ~live () =
  let describe planned =
    Pp.(
      str "field " ++ int field
      ++ str (if as_bound then " of a pattern, declared as bound" else " of a pattern")
      ++ (match (!tctx).body_owner with Some r -> str " in " ++ Names.GlobRef.print r | None -> mt ())
      ++ str ": lowering "
      ++ str (if live then "boxes" else "does not box")
      ++ str ", the plan " ++ str planned)
  in
  match List.find_opt (fun (s, f, _) -> Int.equal f field && Core_binder.equal_site s site) (!tctx).representation with
  | Some (_, _, {pr_boxed; pr_bound_boxed}) ->
    let pr_boxed = if as_bound then pr_bound_boxed else pr_boxed in
    let agrees = pr_boxed = live in
    Probe.hit "repr-plan" (fun () ->
        (if as_bound then "bound " else "")
        ^ (if agrees then "agree " else "disagree ")
        ^ if agrees then if live then "boxed" else "value" else Pp.string_of_ppcmds (describe ""));
    if not agrees then
      Probe.violation "pattern binder representation" (describe (if pr_boxed then "boxes" else "does not"))
  | None -> Probe.violation "pattern binder representation" (describe "has no answer")
