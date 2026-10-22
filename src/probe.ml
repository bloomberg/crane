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

(* The census log, and whether the census writes the files it extracts:
   [write:<log>] does, for the census that compiles them. *)
let census_mode =
  lazy
    ( match Sys.getenv_opt "CRANE_LOOPIFY_CENSUS" with
    | None | Some "" -> None
    | Some v ->
      let writes, path =
        match String.split_on_char ':' v with
        | "write" :: (_ :: _ as rest) -> (true, String.concat ":" rest)
        | _ -> (false, v)
      in
      Some (open_out_gen [Open_wronly; Open_append; Open_creat] 0o644 path, writes) )

let census_log = lazy (Option.map fst (Lazy.force census_mode))
let census () = Option.has_some (Lazy.force census_mode)
let census_dry () = match Lazy.force census_mode with Some (_, writes) -> not writes | None -> false

(* One line per record, written whole, so that the coqc runs dune starts in
   parallel interleave lines rather than characters. *)
let record oc fields =
  let line = String.concat ": " fields in
  output_string oc (String.map (function '\n' -> ' ' | c -> c) line ^ "\n");
  flush oc

let library () = Names.DirPath.to_string (Lib.library_dp ())

let census_unit () =
  Option.iter (fun oc -> record oc ["extracted"; library ()]) (Lazy.force census_log)

let check_ir = lazy (Sys.getenv_opt "CRANE_CHECK_IR" <> None)
let checking () = Lazy.force check_ir || census ()

let violation what detail =
  match Lazy.force census_log with
  | Some oc -> record oc [library (); what; Pp.string_of_ppcmds detail]
  | None ->
    if checking () then
      CErrors.user_err Pp.(str "Crane IR check (" ++ str what ++ str "): " ++ detail)

let hit_at tag r =
  hit tag (fun () -> Pp.string_of_ppcmds (Names.GlobRef.print r))

let changed tag r ~before after =
  if enabled () && before != after && before <> after then hit_at tag r;
  after
