(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

let sink =
  lazy
    (Option.map
       (fun path ->
         open_out_gen [Open_wronly; Open_append; Open_creat] 0o644 path )
       (Sys.getenv_opt "CRANE_PROBE") )

let enabled () = Option.has_some (Lazy.force sink)

let hit tag detail =
  match Lazy.force sink with
  | None -> ()
  | Some oc ->
    output_string oc (tag ^ " " ^ detail () ^ "\n");
    flush oc

let check_ir = lazy (Sys.getenv_opt "CRANE_CHECK_IR" <> None)
let checking () = Lazy.force check_ir

let violation what detail =
  if checking () then
    CErrors.user_err Pp.(str "Crane IR check (" ++ str what ++ str "): " ++ detail)

let hit_at tag r =
  hit tag (fun () -> Pp.string_of_ppcmds (Names.GlobRef.print r))

let changed tag r ~before after =
  if enabled () && before != after && before <> after then hit_at tag r;
  after
