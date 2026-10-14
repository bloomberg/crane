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
  let note r = found := Entity_id.Set.add (Entity_id.of_ref r) !found in
  let ft t =
    ( match t with
    | Tglob (r, _, _) | Tnamespace (r, _) | Tinstance (_, r) -> note r
    | _ -> () );
    t
  in
  let rec fe e =
    ( match e with
    | CPPglob (r, _, _) | CPPnamespace (r, _) | CPPstructmk (r, _, _)
    | CPPstruct (r, _, _) | CPPenum_val (r, _) ->
      note r
    | CPPconcept_app (c, r, _) -> note c; note r
    | _ -> () );
    map_expr fe fs (map_cpp_type ft) e
  and fs s = map_stmt fe fs (map_cpp_type ft) s in
  List.iter (fun d -> ignore (map_decl fe fs (map_cpp_type ft) d)) decls;
  !found

type t = {
  entities : entity list;
  lifted : helper list;
}

let entities t = t.entities
let helpers t = t.lifted

let entity_ids e =
  List.fold_left
    (fun s h -> Id_set.add (Generated h.helper_id) s)
    (Id_set.singleton (Source e.entity_id))
    e.helpers

let ids t =
  List.fold_left
    (fun s e -> Id_set.union s (entity_ids e))
    (Id_set.of_list (List.map (fun h -> Generated h.helper_id) t.lifted))
    t.entities

(** What discovery generated.  Its documents are discarded, and so are its
    declarations: identities are all {!check_emission_matches_discovery}
    reads. *)
let discovered_ids : Id_set.t ref = State.cell State.Unit Id_set.empty

(** Each emitted file's program so far, newest first. *)
let emitted_files : (Common.file, t) Hashtbl.t = State.table State.Unit 2

let add_to_file f update =
  let t = Option.default { entities = []; lifted = [] } (Hashtbl.find_opt emitted_files f) in
  Hashtbl.replace emitted_files f (update t)

let record e =
  ( match Common.get_phase () with
  | Common.Discover -> discovered_ids := Id_set.union !discovered_ids (entity_ids e)
  | Common.Emit f -> add_to_file f (fun t -> { t with entities = e :: t.entities }) );
  e

let record_helper h =
  match Common.get_phase () with
  | Common.Discover -> discovered_ids := Id_set.add (Generated h.helper_id) !discovered_ids
  | Common.Emit f -> add_to_file f (fun t -> { t with lifted = h :: t.lifted })

let discovered () = !discovered_ids

let emitted f =
  match Hashtbl.find_opt emitted_files f with
  | Some t -> { entities = List.rev t.entities; lifted = List.rev t.lifted }
  | None -> { entities = []; lifted = [] }

let check_emission_matches_discovery () =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    let emitted = Id_set.union (ids (emitted Common.Impl)) (ids (emitted Common.Intf)) in
    let report what s =
      if Id_set.is_empty s then Pp.mt ()
      else
        Pp.(
          fnl () ++ str what ++ str ": "
          ++ prlist_with_sep (fun () -> str ", ") pp_id (Id_set.elements s))
    in
    if not (Id_set.equal !discovered_ids emitted) then
      CErrors.anomaly
        Pp.(
          str "Crane: emission generated different entities from discovery."
          ++ report "only in emission" (Id_set.diff emitted !discovered_ids)
          ++ report "only in discovery" (Id_set.diff !discovered_ids emitted))
