(* SPDX-License-Identifier: BSD-3-Clause *)
open XML
open Bench_common

module XML_PR = XML_Parser.ParserAndProofs.PEF.PS.P

let rec count_xml_nodes = function
  | XmlNode (_, _, children) ->
      1 + List.fold_left (fun acc c -> acc + count_xml_nodes c) 0 children
  | XmlLeaf _ -> 1

let fingerprint_xml pr =
  match pr with
  | XML_PR.Coq_unique v | XML_PR.Coq_ambig v ->
      let doc = (Obj.magic v : xml_document) in
      (match doc with XmlDocument (_, elt) -> Some (count_xml_nodes elt))
  | _ -> None

let () =
  Bench_common.ensure_big_stack ();
  try
    let filepath = Sys.argv.(1) in
    let input_cs = chars_from_file filepath in
    let (ts_opt, _) = lex_xml input_cs in
    match ts_opt with
    | None ->
        Printf.eprintf "Lex failure: %s\n%!" filepath;
        exit 1
    | Some ts ->
        let pr = parse_xml ts in
        let meta = {
          parse_result = str_of_coqstr (show_xml_result pr);
          num_tokens   = List.length ts;
          parse_nodes  = fingerprint_xml pr;
          ref_nodes    = None;
        } in
        print_string (metadata_to_json_line meta);
        print_newline ()
  with e ->
    Printf.eprintf "Exception: %s\n%!" (Printexc.to_string e);
    exit 1
