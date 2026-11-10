(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

module Node_table = Hashtbl.Make (struct
  type t = Obj.t

  let equal = ( == )
  let hash = Hashtbl.hash
end)

type key = Obj.t * Minicpp.cpp_decl

let key d : key = (Obj.repr d, d)
let key_of node d : key = (Obj.repr node, d)

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

type job = id * key

let job id key : job = (id, key)

type declaration = {
  id : id;
  finished : Cpp_erasure.settled;
}

type t = {
  declarations : declaration list;
  index : declaration Node_table.t;
      (** Each declaration by the physical identity of what it was finished
          from: how a file's render finds it. *)
  demands : Table.header list;
  globals : Names.GlobRef.t list;
  promoted : Names.Id.t list;
}

let finish jobs =
  let index = Node_table.create 256 in
  let declarations = ref [] and demands = ref [] and globals = ref [] and promoted = ref [] in
  let keys = ref Id_map.empty in
  List.iter
    (fun (id, (node, d)) ->
      ( match Id_map.find_opt id !keys with
      | Some node' when node' != node ->
        Probe.violation "finished program" Pp.(str "two declarations finished as " ++ pp_id id)
      | Some _ | None -> keys := Id_map.add id node !keys );
      match Node_table.find_opt index node with
      | Some d ->
        if compare_id d.id id <> 0 then
          Probe.violation "finished program"
            Pp.(str "one declaration finished as " ++ pp_id d.id ++ str " and as " ++ pp_id id)
      | None ->
        let f = Cpp_pipeline.finish d in
        demands := List.rev_append (Cpp_demands.of_decl (f :> Minicpp.cpp_decl)) !demands;
        globals := List.rev_append (Cpp_demands.globals_of_decl (f :> Minicpp.cpp_decl)) !globals;
        promoted := List.rev_append (Cpp_demands.promoted_of_decl (f :> Minicpp.cpp_decl)) !promoted;
        let declaration = {id; finished = f} in
        declarations := declaration :: !declarations;
        Node_table.replace index node declaration )
    jobs;
  { declarations = List.rev !declarations;
    index;
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
  State.cell State.Unit
    {declarations = []; index = Node_table.create 0; demands = []; globals = []; promoted = []}

let installed_globals () = !installed.globals

let installed_declarations () = List.map (fun d -> d.finished) !installed.declarations

let installed_promoted () = !installed.promoted

let install t = installed := t

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let finishes_as ((_, d) : key) f = compare f (Cpp_pipeline.finish d) = 0

let find ((node, _) : key) = Option.map (fun d -> d.finished) (Node_table.find_opt !installed.index node)

let refinish jobs =
  List.iter
    (fun (id, ((node, _) as key)) ->
      match Node_table.find_opt !installed.index node with
      | Some d when compare_id d.id id = 0 && finishes_as key d.finished -> ()
      | Some _ | None ->
        CErrors.anomaly
          Pp.(str "Crane: a declaration was finished differently again in the reverse order.") )
    jobs
