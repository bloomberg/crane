(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

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
}

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

let push ids scope =
  { lex = Lexenv.push (List.map (fun (x, ty) -> {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = Lexenv.Value}) ids) scope.lex;
    planned = List.map (fun (_, ty) -> at_binding ty) ids @ scope.planned }

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

let region ~outer body =
  let found = ref [] in
  let promoted_active = (!tctx).promoted_var_map <> [] in
  let return = (!tctx).current_cpp_return_type in
  let type_vars = (!tctx).current_type_vars in
  let is_lambda a = match strip_magic a with MLlam _ -> true | _ -> false in
  let rec walk scope = function
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
      let inner = push (List.rev ids) scope in
      walk {inner with planned = List.rev retyped @ scope.planned} body
    | MLcase (ty, scrut, branches, occ) ->
      walk scope scrut;
      let var_type = Lexenv.type_opt scope.lex in
      let fields =
        if Table.is_custom_match branches then
          let cs =
            custom_match_scrutinee (Common.empty_env ()) ty scrut branches
              ~var_boxed:(fun i -> boxed (planned scope i)) ~var_type
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
          let inner = push (List.rev ids) scope in
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
            walk (push ids scope) body
          | _ -> walk scope a )
        args
    | MLletin (x, ty, a, body, _) ->
      walk scope a;
      walk (push [(x, ty)] scope) body
    (* Any other lambda's binders at the types they are annotated with.
       Lowering also declares a parameter by the C++ slot the lambda fills --
       [const auto &], or [std::any] where the slot's domain is a box --
       which the check holds to the same answer for every pattern binder
       rooted at one. *)
    | MLlam _ as e ->
      let ids, body = Mlutil.collect_lams e in
      walk (push ids scope) body
    | MLfix (_, fs, defs, _, _) ->
      let scope = push (List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs)) scope in
      Array.iter (walk scope) defs
    | e -> Mlutil.ast_iter (walk scope) e
  in
  let outer_planned = List.init (Lexenv.depth outer) (fun i -> Option.bind (Lexenv.type_opt outer (i + 1)) at_binding) in
  walk {lex = outer; planned = outer_planned} body;
  !found

let same_site a b =
  match (a, b) with
  | Core_binder.Branch (o, i), Core_binder.Branch (o', i') -> Occurrence.equal o o' && Int.equal i i'
  | Binding o, Binding o' -> Occurrence.equal o o'
  | Branch _, Binding _ | Binding _, Branch _ -> false

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
  match List.find_opt (fun (s, f, _) -> Int.equal f field && same_site s site) (!tctx).representation with
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
