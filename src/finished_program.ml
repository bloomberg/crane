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

let finished : Cpp_erasure.settled Node_table.t = Node_table.create 256

let () = State.on_reset State.Unit (fun () -> Node_table.reset finished)

(* [compare] rather than [=]: a NaN literal is equal to itself. *)
let finishes_as ((_, d) : job) f = compare f (Cpp_pipeline.finish d) = 0

let finish jobs =
  List.iter
    (fun (key, d) ->
      if not (Node_table.mem finished key) then Node_table.replace finished key (Cpp_pipeline.finish d) )
    jobs

let find ((key, _) : job) = Node_table.find_opt finished key

let refinish jobs =
  List.iter
    (fun job ->
      match find job with
      | Some f when finishes_as job f -> ()
      | Some _ | None ->
        CErrors.anomaly
          Pp.(str "Crane: a declaration was finished differently again in the reverse order.") )
    jobs
