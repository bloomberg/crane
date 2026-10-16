(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

module Node_table = Hashtbl.Make (struct
  type t = Obj.t

  let equal = ( == )
  let hash = Hashtbl.hash
end)

type job = Obj.t * Minicpp.cpp_decl

let job d : job = (Obj.repr d, d)
let job_of key d : job = (Obj.repr key, d)

type t = {
  decls : Cpp_erasure.settled Node_table.t;
  demands : Table.header list;
}

let finish jobs =
  let decls = Node_table.create 256 and demands = ref [] in
  List.iter
    (fun (key, d) ->
      if not (Node_table.mem decls key) then begin
        let f = Cpp_pipeline.finish d in
        demands := List.rev_append (Cpp_demands.of_decl (f :> Minicpp.cpp_decl)) !demands;
        Node_table.replace decls key f
      end )
    jobs;
  {decls; demands = List.sort_uniq compare !demands}

let demands t = t.demands

let installed = State.cell State.Unit {decls = Node_table.create 0; demands = []}

let install t = installed := t

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let finishes_as ((_, d) : job) f = compare f (Cpp_pipeline.finish d) = 0

let find ((key, _) : job) = Node_table.find_opt !installed.decls key

let refinish jobs =
  List.iter
    (fun job ->
      match find job with
      | Some f when finishes_as job f -> ()
      | Some _ | None ->
        CErrors.anomaly
          Pp.(str "Crane: a declaration was finished differently again in the reverse order.") )
    jobs
