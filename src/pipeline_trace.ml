(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type 'a pass = { name : string; run : 'a -> 'a }

let pass name run = { name; run }
let effect name f = { name; run = (fun x -> f x; x) }
let names passes = List.map (fun p -> p.name) passes

let enabled =
  let on = lazy (Sys.getenv_opt "CRANE_TRACE_PIPELINE" <> None) in
  fun () -> Lazy.force on

let event stage what =
  if enabled () then
    Feedback.msg_notice (Pp.str (Printf.sprintf "[crane:pipeline] %s: %s" stage what))

let run ~stage passes x =
  List.fold_left (fun x p -> event stage p.name; p.run x) x passes
