(* SPDX-License-Identifier: BSD-3-Clause *)
open JSON
open Bench_common

module JSON_PR = JSON_Parser.ParserAndProofs.PEF.PS.P

let rec count_json_nodes = function
  | JAssoc pairs -> 1 + List.fold_left (fun acc (_, v) -> acc + count_json_nodes v) 0 pairs
  | JList  vs   -> 1 + List.fold_left (fun acc v -> acc + count_json_nodes v) 0 vs
  | _            -> 1

let fingerprint_json pr =
  match pr with
  | JSON_PR.Coq_unique v | JSON_PR.Coq_ambig v ->
      Some (count_json_nodes (Obj.magic v : json_value))
  | _ -> None

let rec count_yojson_nodes = function
  | `Assoc pairs -> 1 + List.fold_left (fun acc (_, v) -> acc + count_yojson_nodes v) 0 pairs
  | `List  vs   -> 1 + List.fold_left (fun acc v -> acc + count_yojson_nodes v) 0 vs
  | _            -> 1

let crossval_json raw =
  try Some (count_yojson_nodes (Yojson.Basic.from_string raw))
  with _ -> None

let () =
  Bench_common.ensure_big_stack ();
  try
    let filepath = Sys.argv.(1) in
    let input_cs = chars_from_file filepath in
    let (ts_opt, _) = lex_json input_cs in
    match ts_opt with
    | None ->
        Printf.eprintf "Lex failure: %s\n%!" filepath;
        exit 1
    | Some ts ->
        let pr = parse_json ts in
        let meta = {
          parse_result = str_of_coqstr (show_json_result pr);
          num_tokens   = List.length ts;
          parse_nodes  = fingerprint_json pr;
          ref_nodes    = crossval_json (raw_str_of_coqstr input_cs);
        } in
        print_string (metadata_to_json_line meta);
        print_newline ()
  with e ->
    Printf.eprintf "Exception: %s\n%!" (Printexc.to_string e);
    exit 1
