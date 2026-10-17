(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

type id =
  | Source of Entity_id.t
  | Generated of Generated_entity_id.t

let compare_id a b =
  match (a, b) with
  | Source x, Source y -> Entity_id.compare x y
  | Generated x, Generated y -> Generated_entity_id.compare x y
  | Source _, Generated _ -> -1
  | Generated _, Source _ -> 1

let pp_id = function
  | Source e -> Entity_id.pp e
  | Generated g -> Generated_entity_id.pp g

module Id_set = Set.Make (struct
  type t = id

  let compare = compare_id
end)

type helper = {
  helper_id : Generated_entity_id.t;
  helper_decl : cpp_decl;
}

type entity = {
  entity_id : Entity_id.t;
  decls : cpp_decl list;
  helpers : helper list;
}

let helper d =
  Option.map
    (fun h -> { helper_id = Generated_entity_id.lifted_helper h; helper_decl = d })
    (Option.bind (decl_globref d) Lifted.of_ref)

let dependencies decls =
  let found = ref Entity_id.Set.empty in
  List.iter
    (Minicpp.iter_globrefs (fun r -> found := Entity_id.Set.add (Entity_id.of_ref r) !found))
    decls;
  !found

type t = {
  entities : entity list;
  lifted : helper list;
}

let entities t = t.entities

let entity_ids e =
  List.fold_left
    (fun s h -> Id_set.add (Generated h.helper_id) s)
    (Id_set.singleton (Source e.entity_id))
    e.helpers

let entities_ids entities =
  List.fold_left (fun s e -> Id_set.union s (entity_ids e)) Id_set.empty entities

let ids t = Id_set.union (Id_set.of_list (List.map (fun h -> Generated h.helper_id) t.lifted)) (entities_ids t.entities)

(** The entities the files have taken so far, either file, newest first. *)
let taken : entity list ref = State.cell State.Unit []

let record e =
  ( match Common.get_phase () with
  | Common.Emit -> taken := e :: !taken
  | Common.Plan -> CErrors.anomaly Pp.(str "Crane: a declaration was generated while planning.") );
  e

(** The unit's program as the walk ahead of the files generated it, newest
    first: its entities, and every helper its generations lifted. *)
let generated_ahead : t ref = State.cell State.Unit { entities = []; lifted = [] }

(* A helper is lifted by one generation: the same declaration may be handed
   on -- a method's helpers to the inductive that takes the method -- but a
   second declaration of the same helper is a second generation of it, and
   both would be written. *)
let record_helper_ahead h =
  let t = !generated_ahead in
  match
    List.find_opt (fun h' -> Generated_entity_id.equal h'.helper_id h.helper_id) t.lifted
  with
  | None -> generated_ahead := { t with lifted = h :: t.lifted }
  | Some h' ->
    if h'.helper_decl != h.helper_decl then
      let id = Generated_entity_id.pp h.helper_id in
      Probe.violation "lifted helpers" Pp.(str "two generations lifted the helper " ++ id)

let record_lifted_ahead ds = List.iter (fun d -> Option.iter record_helper_ahead (helper d)) ds

let record_ahead e =
  List.iter record_helper_ahead e.helpers;
  generated_ahead := { !generated_ahead with entities = e :: !generated_ahead.entities }

let check_against_plan ~declares =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    let emitted = Id_set.union (ids !generated_ahead) (entities_ids !taken) in
    let planned = function
      | Source e -> declares (Entity_id.to_ref e)
      | Generated g -> (
        match Generated_entity_id.owner g with
        | None -> true
        | Some e -> declares (Entity_id.to_ref e) || Id_set.mem (Source e) emitted )
    in
    let unplanned = Id_set.filter (fun id -> not (planned id)) emitted in
    if not (Id_set.is_empty unplanned) then
      CErrors.anomaly
        Pp.(
          str "Crane: emission generated entities the plan does not account for: "
          ++ prlist_with_sep (fun () -> str ", ") pp_id (Id_set.elements unplanned))

let check_against_ahead () =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    let taken = entities_ids !taken in
    let ahead = entities_ids !generated_ahead.entities in
    if not (Id_set.equal taken ahead) then
      let show s = Pp.(prlist_with_sep (fun () -> str ", ") pp_id (Id_set.elements s)) in
      CErrors.anomaly
        Pp.(
          str "Crane: the files took other entities than were generated ahead of them; ahead only: "
          ++ show (Id_set.diff ahead taken)
          ++ str "; taken only: "
          ++ show (Id_set.diff taken ahead) )
