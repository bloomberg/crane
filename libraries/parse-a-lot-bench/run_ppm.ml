(* SPDX-License-Identifier: BSD-3-Clause *)
open PPM
open Bench_common

module PPM_PR = PPM_Parser.ParserAndProofs.PEF.PS.P

(* Pixel count = List.length ppm.triples, independently verifiable as width × height *)
let fingerprint_ppm pr =
  match pr with
  | PPM_PR.Coq_unique v | PPM_PR.Coq_ambig v ->
      let ppm = (Obj.magic v : ppm_value) in
      Some (List.length ppm.triples)
  | _ -> None

let () =
  Bench_common.ensure_big_stack ();
  try
    let filepath = Sys.argv.(1) in
    let input_cs = chars_from_file filepath in
    let (ts_opt, _) = lex_ppm input_cs in
    match ts_opt with
    | None ->
        Printf.eprintf "Lex failure: %s\n%!" filepath;
        exit 1
    | Some ts ->
        let pr = parse_ppm ts in
        let meta = {
          parse_result = str_of_coqstr (show_ppm_result pr);
          num_tokens   = List.length ts;
          parse_nodes  = fingerprint_ppm pr;
          ref_nodes    = None;
        } in
        print_string (metadata_to_json_line meta);
        print_newline ()
  with e ->
    Printf.eprintf "Exception: %s\n%!" (Printexc.to_string e);
    exit 1
