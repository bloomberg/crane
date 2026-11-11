(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type part =
  | Declaration of int
  | Methods

type id = {
  owner : Generated_program.id;
  part : part;
}

let compare_id a b =
  match Generated_program.compare_id a.owner b.owner with 0 -> compare a.part b.part | c -> c

let pp_id {owner; part} =
  Pp.(Generated_program.pp_id owner ++ match part with Declaration n -> str "#" ++ int n | Methods -> str "#methods")

module Id_map = Map.Make (struct
  type t = id

  let compare = compare_id
end)

type job = id * Minicpp.cpp_decl

let job id d : job = (id, d)

type declaration = {
  id : id;
  finished : Cpp_erasure.settled;
}

type t = {
  declarations : declaration list;
  by_id : Cpp_erasure.settled Id_map.t;
      (** Each declaration by its id: how a file's render finds it. *)
  demands : Table.header list;
  globals : Names.GlobRef.t list;
  promoted : Names.Id.t list;
}

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let same_source d d' = d == d' || compare d d' = 0

let finish jobs =
  let declarations = ref [] and demands = ref [] and globals = ref [] and promoted = ref [] in
  let sources = ref Id_map.empty and by_id = ref Id_map.empty in
  List.iter
    (fun (id, d) ->
      match Id_map.find_opt id !sources with
      | Some d' ->
        if Probe.checking () && not (same_source d d') then
          Probe.violation "finished program" Pp.(str "two declarations finished as " ++ pp_id id)
      | None ->
        let f = Cpp_pipeline.finish d in
        demands := List.rev_append (Cpp_demands.of_decl (f :> Minicpp.cpp_decl)) !demands;
        globals := List.rev_append (Cpp_demands.globals_of_decl (f :> Minicpp.cpp_decl)) !globals;
        promoted := List.rev_append (Cpp_demands.promoted_of_decl (f :> Minicpp.cpp_decl)) !promoted;
        declarations := {id; finished = f} :: !declarations;
        sources := Id_map.add id d !sources;
        by_id := Id_map.add id f !by_id )
    jobs;
  { declarations = List.rev !declarations;
    by_id = !by_id;
    demands = List.sort_uniq compare !demands;
    globals = !globals;
    promoted = List.rev !promoted }

let declarations t = t.declarations

let helpers t =
  List.filter_map
    (fun {id; finished} ->
      match id.owner with Generated_program.Generated h -> Some (h, finished) | Source _ -> None)
    t.declarations

let demands t = t.demands
let globals t = t.globals

let check_against_generated t =
  if Probe.checking () then begin
    let generated = Generated_program.generated_ahead_ids () in
    let owners = Generated_program.Id_set.of_list (List.map (fun d -> d.id.owner) t.declarations) in
    let show s = Pp.(prlist_with_sep (fun () -> str ", ") Generated_program.pp_id (Generated_program.Id_set.elements s)) in
    let unowned = Generated_program.Id_set.diff owners generated in
    if not (Generated_program.Id_set.is_empty unowned) then
      Probe.violation "finished program"
        Pp.(str "declarations finished for entities the unit did not generate: " ++ show unowned);
    let unfinished =
      Generated_program.Id_set.filter
        (function Generated_program.Generated _ as id -> not (Generated_program.Id_set.mem id owners) | Source _ -> false)
        generated
    in
    if not (Generated_program.Id_set.is_empty unfinished) then
      Probe.violation "finished program" Pp.(str "helpers generated and not finished: " ++ show unfinished)
  end

let installed =
  State.cell State.Unit {declarations = []; by_id = Id_map.empty; demands = []; globals = []; promoted = []}

let installed_globals () = !installed.globals

let installed_declarations () = List.map (fun d -> d.finished) !installed.declarations

let installed_promoted () = !installed.promoted

let install t = installed := t

let finishes_as d f = compare f (Cpp_pipeline.finish d) = 0

let find id = Id_map.find_opt id !installed.by_id

let refinish jobs =
  List.iter
    (fun (id, d) ->
      match find id with
      | Some f when finishes_as d f -> ()
      | Some _ | None ->
        CErrors.anomaly
          Pp.(str "Crane: a declaration was finished differently again in the reverse order.") )
    jobs
