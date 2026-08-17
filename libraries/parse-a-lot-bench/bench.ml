(* SPDX-License-Identifier: BSD-3-Clause *)
open Bench_common
module Yb = Yojson.Basic
module Yu = Yojson.Basic.Util

(***********************************************************************)
(* Argument parsing                                                    *)
(***********************************************************************)

type bench_args = {
  lang     : string;
  data_dir : string;
  outfile  : string;
  warmup   : int option;
  runs     : int option;
}

let parse_args () =
  let argv = Sys.argv in
  let n = Array.length argv in
  if n < 4 then begin
    Printf.eprintf "Usage: %s -json|-xml|-newick|-ppm <data_dir> <output_json> [--warmup N] [--runs N]\n%!" argv.(0);
    exit 1
  end;
  let lang     = argv.(1) in
  let data_dir = argv.(2) in
  let outfile  = argv.(3) in
  let warmup   = ref None in
  let runs     = ref None in
  let i = ref 4 in
  while !i < n do
    (match argv.(!i) with
     | "--warmup" when !i + 1 < n ->
         warmup := Some (int_of_string argv.(!i + 1));
         i := !i + 2
     | "--runs" when !i + 1 < n ->
         runs := Some (int_of_string argv.(!i + 1));
         i := !i + 2
     | arg ->
         Printf.eprintf "Unknown argument: %s\n%!" arg;
         exit 1)
  done;
  { lang; data_dir; outfile; warmup = !warmup; runs = !runs }

(***********************************************************************)
(* Locating runner executables                                         *)
(***********************************************************************)

let runner_of_lang lang =
  let bin_dir = Filename.dirname Sys.argv.(0) in
  let name = match lang with
    | "-json"   -> "run_json.exe"
    | "-xml"    -> "run_xml.exe"
    | "-newick" -> "run_newick.exe"
    | "-ppm"    -> "run_ppm.exe"
    | l -> failwith ("Unknown language flag: " ^ l)
  in
  Filename.concat bin_dir name

let ref_runner_of_lang lang =
  let bin_dir = Filename.dirname Sys.argv.(0) in
  let name = match lang with
    | "-json"   -> Some "run_json_ref.exe"
    | "-xml"    -> Some "run_xml_ref.exe"
    | "-newick" -> Some "run_newick_ref.exe"
    | "-ppm"    -> Some "run_ppm_ref.exe"
    | _         -> None
  in
  match name with
  | None -> None
  | Some n ->
      let path = Filename.concat bin_dir n in
      if Sys.file_exists path then Some path else None

let crane_runner_of_lang lang =
  let bin_dir = Filename.dirname Sys.argv.(0) in
  let name = match lang with
    | "-json"   -> Some "run_json_crane.exe"
    | "-xml"    -> Some "run_xml_crane.exe"
    | "-newick" -> Some "run_newick_crane.exe"
    | "-ppm"    -> Some "run_ppm_crane.exe"
    | _         -> None
  in
  match name with
  | None -> None
  | Some n ->
      let path = Filename.concat bin_dir n in
      if Sys.file_exists path then Some path else None

(***********************************************************************)
(* Metadata pass: run the runner once, capture stdout                  *)
(***********************************************************************)

let get_metadata runner filepath =
  let cmd = Printf.sprintf "%s %s"
    (Filename.quote runner) (Filename.quote filepath) in
  let ic = Unix.open_process_in cmd in
  let line = try input_line ic with End_of_file -> "" in
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 0 -> Some (metadata_of_json_line line)
  | _ -> None

(***********************************************************************)
(* Timing pass: call hyperfine                                         *)
(***********************************************************************)

type timing_stats = {
  mean        : float;
  stddev      : float;
  median      : float;
  user        : float;
  system_time : float;
  min_time    : float;
  max_time    : float;
  times       : float list;
  exit_codes  : int list;
}

let parse_hyperfine_json json =
  let results = json |> Yu.member "results" |> Yu.to_list in
  List.filter_map (fun r ->
    try Some {
      mean        = r |> Yu.member "mean"   |> Yu.to_float;
      stddev      = r |> Yu.member "stddev" |> Yu.to_float;
      median      = r |> Yu.member "median" |> Yu.to_float;
      user        = r |> Yu.member "user"   |> Yu.to_float;
      system_time = r |> Yu.member "system" |> Yu.to_float;
      min_time    = r |> Yu.member "min"    |> Yu.to_float;
      max_time    = r |> Yu.member "max"    |> Yu.to_float;
      times       = r |> Yu.member "times"  |> Yu.to_list
                      |> List.map Yu.to_float;
      exit_codes  = r |> Yu.member "exit_codes" |> Yu.to_list
                      |> List.map Yu.to_int;
    }
    with _ -> None
  ) results

let run_hyperfine runner ref_runner_opt crane_runner_opt filepath warmup runs =
  let tmp = Filename.temp_file "bench_hf_" ".json" in
  let warmup_flag = match warmup with
    | Some n -> Printf.sprintf "--warmup %d " n
    | None   -> "" in
  let runs_flag = match runs with
    | Some n -> Printf.sprintf "--runs %d " n
    | None   -> "" in
  let bench_cmd = Printf.sprintf "%s %s" runner filepath in
  let ref_cmd_str = match ref_runner_opt with
    | None -> ""
    | Some rr ->
        " " ^ Filename.quote (Printf.sprintf "%s %s" rr filepath)
  in
  let crane_cmd_str = match crane_runner_opt with
    | None -> ""
    | Some cr ->
        " " ^ Filename.quote (Printf.sprintf "%s %s" cr filepath)
  in
  let cmd = Printf.sprintf
    "hyperfine --shell=none --ignore-failure %s%s--export-json %s %s%s%s"
    warmup_flag runs_flag
    (Filename.quote tmp)
    (Filename.quote bench_cmd)
    ref_cmd_str
    crane_cmd_str in
  let rc = Sys.command cmd in
  if rc <> 0 then begin
    (try Sys.remove tmp with _ -> ());
    []
  end else
    let json = Yb.from_file tmp in
    Sys.remove tmp;
    parse_hyperfine_json json

(***********************************************************************)
(* Combined output record                                              *)
(***********************************************************************)

type bench_record = {
  filename           : string;
  num_tokens         : int;
  parse_result       : string;
  parse_nodes        : int option;
  ref_nodes          : int option;
  crane_parse_result : string option;
  crane_parse_nodes  : int option;
  results_match      : bool option;  (* None = no crane runner; Some b = OCaml vs C++ agree *)
  timing             : timing_stats;
  ref_timing         : timing_stats option;
  crane_timing       : timing_stats option;
}

(* Compare OCaml and C++ (crane) parse metadata for the same input.
   [None] crane metadata means the C++ runner failed to emit a result line. *)
let compute_results_match (ocaml_meta : parse_metadata)
    (crane_meta : parse_metadata option) : bool option =
  match crane_meta with
  | None -> Some false
  | Some cm ->
      Some (ocaml_meta.parse_result = cm.parse_result
            && ocaml_meta.parse_nodes = cm.parse_nodes)

let json_of_timing_fields prefix t =
  [ (prefix ^ "mean",       `Float t.mean)
  ; (prefix ^ "stddev",     `Float t.stddev)
  ; (prefix ^ "median",     `Float t.median)
  ; (prefix ^ "user",       `Float t.user)
  ; (prefix ^ "system",     `Float t.system_time)
  ; (prefix ^ "min",        `Float t.min_time)
  ; (prefix ^ "max",        `Float t.max_time)
  ; (prefix ^ "times",      `List (List.map (fun f -> `Float f) t.times))
  ; (prefix ^ "exit_codes", `List (List.map (fun c -> `Int c) t.exit_codes))
  ]

let json_of_string_opt = function
  | None   -> `Null
  | Some s -> `String s

let json_of_bool_opt = function
  | None   -> `Null
  | Some b -> `Bool b

let json_of_bench_record r =
  let base =
    [ ("filename",           `String r.filename)
    ; ("num_tokens",         `Int    r.num_tokens)
    ; ("parse_result",       `String r.parse_result)
    ; ("parse_nodes",        json_of_int_opt r.parse_nodes)
    ; ("ref_nodes",          json_of_int_opt r.ref_nodes)
    ; ("crane_parse_result", json_of_string_opt r.crane_parse_result)
    ; ("crane_parse_nodes",  json_of_int_opt r.crane_parse_nodes)
    ; ("results_match",      json_of_bool_opt r.results_match)
    ] @ json_of_timing_fields "" r.timing
  in
  let ref_fields = match r.ref_timing with
    | None   -> []
    | Some t -> json_of_timing_fields "ref_" t
  in
  let crane_fields = match r.crane_timing with
    | None   -> []
    | Some t -> json_of_timing_fields "crane_" t
  in
  `Assoc (base @ ref_fields @ crane_fields)

(***********************************************************************)
(* Main loop                                                           *)
(***********************************************************************)

let () =
  let args = parse_args () in
  let runner = runner_of_lang args.lang in
  let ref_runner = ref_runner_of_lang args.lang in
  let crane_runner = crane_runner_of_lang args.lang in
  let files = Sys.readdir args.data_dir in
  Array.sort String.compare files;
  let total = Array.length files in
  let results = ref [] in
  Array.iteri (fun i fname ->
    let filepath = Filename.concat args.data_dir fname in
    Printf.printf "[%d/%d] %s\n%!" (i + 1) total fname;

    (* Metadata pass *)
    match get_metadata runner filepath with
    | None ->
        Printf.eprintf "  SKIPPED (lex/parse failure)\n%!"
    | Some meta ->
        (* Cross-check pass: run the C++ (crane) runner and compare results. *)
        let crane_meta = match crane_runner with
          | None    -> None
          | Some cr -> get_metadata cr filepath
        in
        let results_match = match crane_runner with
          | None   -> None
          | Some _ -> compute_results_match meta crane_meta
        in
        (match results_match with
         | Some false ->
             (match crane_meta with
              | None ->
                  Printf.eprintf
                    "  RESULT MISMATCH: C++ produced no result (crash/parse failure)\n%!"
              | Some cm ->
                  Printf.eprintf
                    "  RESULT MISMATCH: ocaml=(%s, nodes=%s) vs crane=(%s, nodes=%s)\n%!"
                    meta.parse_result
                    (match meta.parse_nodes  with Some n -> string_of_int n | None -> "-")
                    cm.parse_result
                    (match cm.parse_nodes    with Some n -> string_of_int n | None -> "-"))
         | Some true  -> Printf.printf "  results match (OCaml == C++)\n%!"
         | None       -> ());

        (* Timing pass *)
        match run_hyperfine runner ref_runner crane_runner filepath args.warmup args.runs with
        | [] ->
            Printf.eprintf "  SKIPPED (hyperfine failure)\n%!"
        | timing :: rest ->
            let (ref_timing, crane_timing) =
              match (ref_runner, crane_runner, rest) with
              | (Some _, Some _, r :: c :: _) -> (Some r, Some c)
              | (Some _, None,   r :: _)      -> (Some r, None)
              | (None,   Some _, c :: _)      -> (None,   Some c)
              | _                             -> (None,   None)
            in
            let record = {
              filename           = fname;
              num_tokens         = meta.num_tokens;
              parse_result       = meta.parse_result;
              parse_nodes        = meta.parse_nodes;
              ref_nodes          = meta.ref_nodes;
              crane_parse_result = (match crane_meta with Some cm -> Some cm.parse_result | None -> None);
              crane_parse_nodes  = (match crane_meta with Some cm -> cm.parse_nodes | None -> None);
              results_match;
              timing;
              ref_timing;
              crane_timing;
            } in
            results := record :: !results
  ) files;

  (* Sort by num_tokens ascending *)
  let sorted = List.sort
    (fun a b -> compare a.num_tokens b.num_tokens)
    !results in
  let json = `List (List.map json_of_bench_record sorted) in
  Yb.to_file args.outfile json;
  Printf.printf "\nResults written to %s (%d entries)\n%!" args.outfile (List.length sorted);

  (* Cross-check summary: how many files had OCaml and C++ agree. *)
  let checked  = List.filter (fun r -> r.results_match <> None) sorted in
  let mismatch = List.filter (fun r -> r.results_match = Some false) checked in
  if checked <> [] then begin
    Printf.printf "OCaml vs C++ result check: %d/%d matched%s\n%!"
      (List.length checked - List.length mismatch)
      (List.length checked)
      (if mismatch = [] then ""
       else Printf.sprintf ", %d MISMATCHED: %s"
              (List.length mismatch)
              (String.concat ", " (List.map (fun r -> r.filename) mismatch)))
  end
