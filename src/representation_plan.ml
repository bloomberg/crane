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
  slot_rooted : bool list;
      (* bound by a lambda inside the region, whose representation lowering
         takes from the slot the lambda fills, or by a pattern over a
         scrutinee that is such a binder *)
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

let push ?(slot_rooted = false) ids scope =
  { lex = Lexenv.push (List.map (fun (x, ty) -> {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = Lexenv.Value}) ids) scope.lex;
    planned = List.map (fun (_, ty) -> at_binding ty) ids @ scope.planned;
    slot_rooted = List.map (fun _ -> slot_rooted) ids @ scope.slot_rooted }

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
  let rec walk scope = function
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
          let slot_rooted =
            match scrutinee_binder scope.lex scrut with
            | Some i -> Option.default false (List.nth_opt scope.slot_rooted (i - 1))
            | None -> false
          in
          let inner = push ~slot_rooted (List.rev ids) scope in
          let inner =
            match pat with
            | Pusual r | Pcons (r, _) when ids <> [] ->
              let field_planned = fields r ids in
              List.iteri
                (fun i p ->
                  found := (Core_binder.Branch (occ, bi), i, {pr_boxed = boxed p; pr_slot_rooted = slot_rooted}) :: !found )
                field_planned;
              {inner with planned = List.rev field_planned @ scope.planned}
            | _ -> inner
          in
          walk inner body )
        branches
    | MLletin (x, ty, a, body, _) ->
      walk scope a;
      walk (push [(x, ty)] scope) body
    (* A lambda's parameter is given the type of the slot the lambda fills
       where lowering builds it -- a [const auto &] at a box, the callee's
       domain at its instance -- which nothing here plans yet. *)
    | MLlam _ as e ->
      let ids, body = Mlutil.collect_lams e in
      walk (push ~slot_rooted:true ids scope) body
    | MLfix (_, fs, defs, _, _) ->
      let scope = push (List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs)) scope in
      Array.iter (walk scope) defs
    | e -> Mlutil.ast_iter (walk scope) e
  in
  let outer_planned = List.init (Lexenv.depth outer) (fun i -> Option.bind (Lexenv.type_opt outer (i + 1)) at_binding) in
  walk {lex = outer; planned = outer_planned; slot_rooted = List.map (fun _ -> false) outer_planned} body;
  !found

let same_site a b =
  match (a, b) with
  | Core_binder.Branch (o, i), Core_binder.Branch (o', i') -> Occurrence.equal o o' && Int.equal i i'
  | Binding o, Binding o' -> Occurrence.equal o o'
  | Branch _, Binding _ | Binding _, Branch _ -> false

let check ~site ~field ~live =
  let describe planned =
    Pp.(
      str "field " ++ int field ++ str " of a pattern"
      ++ (match (!tctx).body_owner with Some r -> str " in " ++ Names.GlobRef.print r | None -> mt ())
      ++ str ": lowering "
      ++ str (if live then "boxes" else "does not box")
      ++ str ", the plan " ++ str planned)
  in
  match List.find_opt (fun (s, f, _) -> Int.equal f field && same_site s site) (!tctx).representation with
  | Some (_, _, {pr_boxed; pr_slot_rooted}) ->
    let agrees = pr_boxed = live in
    Probe.hit "repr-plan" (fun () ->
        (if pr_slot_rooted then "slot-rooted " else "")
        ^ (if agrees then "agree " else "disagree ")
        ^ if agrees then if live then "boxed" else "value" else Pp.string_of_ppcmds (describe ""));
    if not (agrees || pr_slot_rooted) then
      Probe.violation "pattern binder representation" (describe (if pr_boxed then "boxes" else "does not"))
  | None -> Probe.violation "pattern binder representation" (describe "has no answer")
