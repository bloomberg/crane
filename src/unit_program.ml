(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

type owner =
  | Source of Entity_id.t
  | Generated of Generated_entity_id.t

let compare_owner a b =
  match (a, b) with
  | Source x, Source y -> Entity_id.compare x y
  | Generated x, Generated y -> Generated_entity_id.compare x y
  | Source _, Generated _ -> -1
  | Generated _, Source _ -> 1

let pp_owner = function
  | Source e -> Entity_id.pp e
  | Generated g -> Generated_entity_id.pp g

module Owner_set = Set.Make (struct
  type t = owner

  let compare = compare_owner
end)

type part =
  | Declaration of int
  | Methods

type id = {
  owner : owner;
  part : part;
}

let compare_id a b = match compare_owner a.owner b.owner with 0 -> compare a.part b.part | c -> c

let pp_id {owner; part} =
  Pp.(pp_owner owner ++ match part with Declaration n -> str "#" ++ int n | Methods -> str "#methods")

module Id_set = Set.Make (struct
  type t = id

  let compare = compare_id
end)

module Id_map = Map.Make (struct
  type t = id

  let compare = compare_id
end)

type helper = {
  helper_id : Generated_entity_id.t;
  helper_decl : cpp_decl;
}

let helper_declaration h = {owner = Generated h.helper_id; part = Declaration 0}

type entity = {
  entity_id : Entity_id.t;
  declarations : id list;
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

type job = id * cpp_decl

let job id d : job = (id, d)

type declaration = {
  id : id;
  finished : Cpp_ir.Resolved.Decl.t;
}

type t = {
  entities : entity list;
      (** The source declarations' generations, newest first. *)
  lifted : helper list;
      (** Every helper the generations lifted, newest first. *)
  declarations : declaration list;
      (** The finished declarations, in the order they were finished. *)
  by_id : declaration Id_map.t;
      (** Each finished declaration by its id: how a file's render finds
          it. *)
  demands : Table.header list;
      (** The headers the finished declarations need, sorted, each once. *)
  globals : Names.GlobRef.t list;
      (** The globals the finished declarations write the names of. *)
  promoted : Names.Id.t list;
      (** The promoted type variables the finished declarations write, in
          the order finished. *)
}

let empty =
  {entities = []; lifted = []; declarations = []; by_id = Id_map.empty; demands = []; globals = []; promoted = []}

let entities t = List.rev t.entities
let declarations t = t.declarations

let helpers t =
  List.filter_map
    (fun {id; finished; _} -> match id.owner with Generated h -> Some (h, finished) | Source _ -> None)
    t.declarations

let demands t = t.demands
let globals t = t.globals

(* The owners of an entity and of the helpers it claimed. *)
let entity_owners e =
  List.fold_left
    (fun s h -> Owner_set.add (Generated h.helper_id) s)
    (Owner_set.singleton (Source e.entity_id))
    e.helpers

let entities_owners entities =
  List.fold_left (fun s e -> Owner_set.union s (entity_owners e)) Owner_set.empty entities

let owners t =
  Owner_set.union
    (Owner_set.of_list (List.map (fun h -> Generated h.helper_id) t.lifted))
    (entities_owners t.entities)

(* The declarations the generations recorded in [t] give to finish: each
   entity's own, and the declaration of every helper an entity claimed or
   [t] recorded as lifted. *)
let generated_declarations t =
  let of_entity s (e : entity) =
    List.fold_left (fun s h -> Id_set.add (helper_declaration h) s) (Id_set.union s (Id_set.of_list e.declarations)) e.helpers
  in
  List.fold_left (fun s h -> Id_set.add (helper_declaration h) s) (List.fold_left of_entity Id_set.empty t.entities) t.lifted

(** The unit's program: the generations recorded ahead of the files as the
    walk records them, then, once installed, what they finished as. *)
let program : t ref = State.cell State.Unit empty

(** The entities the files have taken so far, either file, newest first. *)
let taken : entity list ref = State.cell State.Unit []

let record e =
  ( match Common.get_phase () with
  | Common.Emit -> taken := e :: !taken
  | Common.Plan -> CErrors.anomaly Pp.(str "Crane: a declaration was generated while planning.") );
  e

(* A helper is lifted by one generation: the same declaration may be handed
   on -- a method's helpers to the inductive that takes the method -- but a
   second declaration of the same helper is a second generation of it, and
   both would be written. *)
let record_helper_ahead h =
  let t = !program in
  match List.find_opt (fun h' -> Generated_entity_id.equal h'.helper_id h.helper_id) t.lifted with
  | None -> program := { t with lifted = h :: t.lifted }
  | Some h' ->
    if h'.helper_decl != h.helper_decl then
      let id = Generated_entity_id.pp h.helper_id in
      Probe.violation "lifted helpers" Pp.(str "two generations lifted the helper " ++ id)

let record_lifted_ahead ds = List.iter (fun d -> Option.iter record_helper_ahead (helper d)) ds

let record_ahead e =
  List.iter record_helper_ahead e.helpers;
  program := { !program with entities = e :: !program.entities }

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let same_source d d' = d == d' || compare d d' = 0

(* The finished declaration [f], [id] of the program, in CppIR.  Every
   finished declaration converts, holding no form only a lowered declaration
   may; each conversion is a probe hit, so that a sweep counts them. *)
let converted id f =
  match Legacy_minicpp_to_cpp_ir.convert f with
  | Ok ir ->
    Probe.hit "cpp_ir" (fun () -> "converted");
    ir
  | Error e ->
    CErrors.anomaly Pp.(str "Crane: " ++ str (Legacy_minicpp_to_cpp_ir.describe e) ++ str " in " ++ pp_id id ++ str ".")

let finish jobs =
  let declarations = ref [] and demands = ref [] and globals = ref [] and promoted = ref [] in
  let sources = ref Id_map.empty and by_id = ref Id_map.empty in
  List.iter
    (fun (id, d) ->
      match Id_map.find_opt id !sources with
      | Some d' ->
        if Probe.checking () && not (same_source d d') then
          Probe.violation "unit program" Pp.(str "two declarations finished as " ++ pp_id id)
      | None ->
        let finished = converted id (Cpp_pipeline.finish d) in
        demands := List.rev_append (Cpp_demands.of_decl finished) !demands;
        globals := List.rev_append (Cpp_demands.globals_of_decl finished) !globals;
        promoted := List.rev_append (Cpp_demands.promoted_of_decl finished) !promoted;
        declarations := {id; finished} :: !declarations;
        sources := Id_map.add id d !sources;
        by_id := Id_map.add id {id; finished} !by_id )
    jobs;
  { !program with
    declarations = List.rev !declarations;
    by_id = !by_id;
    demands = List.sort_uniq compare !demands;
    globals = !globals;
    promoted = List.rev !promoted }

let check_finished t =
  if Probe.checking () then begin
    let generated = generated_declarations t in
    let finished = Id_set.of_list (List.map (fun d -> d.id) t.declarations) in
    let show s = Pp.(prlist_with_sep (fun () -> str ", ") pp_id (Id_set.elements s)) in
    let ungenerated = Id_set.diff finished generated in
    if not (Id_set.is_empty ungenerated) then
      Probe.violation "unit program"
        Pp.(str "declarations finished that no generation of the unit gave: " ++ show ungenerated);
    let unfinished = Id_set.diff generated finished in
    if not (Id_set.is_empty unfinished) then
      Probe.violation "unit program" Pp.(str "declarations generated and not finished: " ++ show unfinished)
  end

let install t = program := t

let installed_globals () = !program.globals

let installed_finished () = List.map (fun d -> d.finished) !program.declarations

let installed_promoted () = !program.promoted

let finishes_as d f =
  match Legacy_minicpp_to_cpp_ir.convert (Cpp_pipeline.finish d) with
  | Ok ir -> compare f ir = 0
  | Error _ -> false

let find_declaration id = Id_map.find_opt id !program.by_id

let find id = Option.map (fun d -> d.finished) (find_declaration id)

let refinish jobs =
  List.iter
    (fun (id, d) ->
      match find id with
      | Some f when finishes_as d f -> ()
      | Some _ | None ->
        CErrors.anomaly
          Pp.(str "Crane: a declaration was finished differently again in the reverse order.") )
    jobs

let check_against_plan ~declares =
  if Probe.checking () then
    let emitted = Owner_set.union (owners !program) (entities_owners !taken) in
    let planned = function
      | Source e -> declares (Entity_id.to_ref e)
      | Generated g -> (
        match Generated_entity_id.owner g with
        | None -> true
        | Some e -> declares (Entity_id.to_ref e) || Owner_set.mem (Source e) emitted )
    in
    let unplanned = Owner_set.filter (fun id -> not (planned id)) emitted in
    if not (Owner_set.is_empty unplanned) then
      CErrors.anomaly
        Pp.(
          str "Crane: emission generated entities the plan does not account for: "
          ++ prlist_with_sep (fun () -> str ", ") pp_owner (Owner_set.elements unplanned))

let check_against_ahead () =
  if Probe.checking () then
    let declarations es = List.fold_left (fun s (e : entity) -> Id_set.union s (Id_set.of_list e.declarations)) Id_set.empty es in
    let taken_owners = entities_owners !taken and ahead_owners = entities_owners !program.entities in
    let taken_declarations = declarations !taken and ahead_declarations = declarations !program.entities in
    if not (Owner_set.equal taken_owners ahead_owners && Id_set.equal taken_declarations ahead_declarations) then
      let show pp elements s = Pp.(prlist_with_sep (fun () -> str ", ") pp (elements s)) in
      let owners = show pp_owner Owner_set.elements and ids = show pp_id Id_set.elements in
      CErrors.anomaly
        Pp.(
          str "Crane: the files took other entities than were generated ahead of them; ahead only: "
          ++ owners (Owner_set.diff ahead_owners taken_owners)
          ++ str " "
          ++ ids (Id_set.diff ahead_declarations taken_declarations)
          ++ str "; taken only: "
          ++ owners (Owner_set.diff taken_owners ahead_owners)
          ++ str " "
          ++ ids (Id_set.diff taken_declarations ahead_declarations) )
