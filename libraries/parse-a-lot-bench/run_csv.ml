(* SPDX-License-Identifier: BSD-3-Clause *)
open CSV
open Bench_common

module CSV_PR = CSV_Parser.ParserAndProofs.PEF.PS.P

(* Fingerprint = total number of fields (sum of record lengths). The parsed
   value is [csv_value = list (list string)]; we only need its shape to count
   fields, so the element type is left polymorphic. *)
let count_fields (rows : _ list list) =
  List.fold_left (fun acc r -> acc + List.length r) 0 rows

let fingerprint_csv pr =
  match pr with
  | CSV_PR.Coq_unique v | CSV_PR.Coq_ambig v ->
      Some (count_fields (Obj.magic v))
  | _ -> None

let () =
  Bench_common.ensure_big_stack ();
  try
    let filepath = Sys.argv.(1) in
    let input_cs = chars_from_file filepath in
    let (ts_opt, _) = lex_csv input_cs in
    match ts_opt with
    | None ->
        Printf.eprintf "Lex failure: %s\n%!" filepath;
        exit 1
    | Some ts ->
        let pr = parse_csv ts in
        let meta = {
          parse_result = str_of_coqstr (show_csv_result pr);
          num_tokens   = List.length ts;
          parse_nodes  = fingerprint_csv pr;
          ref_nodes    = None;  (* no third-party CSV reference baseline *)
        } in
        print_string (metadata_to_json_line meta);
        print_newline ()
  with e ->
    Printf.eprintf "Exception: %s\n%!" (Printexc.to_string e);
    exit 1
