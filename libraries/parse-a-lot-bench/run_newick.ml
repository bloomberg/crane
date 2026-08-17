(* SPDX-License-Identifier: BSD-3-Clause *)
open Newick
open Bench_common

module Newick_PR = Newick_Parser.ParserAndProofs.PEF.PS.P

(* NkTree is a single-constructor inductive unwrapped by Coq extraction.
   nt_semty Trees = list newick_tree extracts to newick_node list list. *)
let rec count_newick_node = function
  | NkLeaf _                -> 1
  | NkINode (descendants, _) ->
      1 + List.fold_left (fun acc n -> acc + count_newick_node n) 0 descendants

let fingerprint_newick pr =
  match pr with
  | Newick_PR.Coq_unique v | Newick_PR.Coq_ambig v ->
      let trees = (Obj.magic v : newick_node list list) in
      Some (List.fold_left
              (fun acc tree ->
                 List.fold_left (fun acc2 n -> acc2 + count_newick_node n) acc tree)
              0 trees)
  | _ -> None

let () =
  Bench_common.ensure_big_stack ();
  try
    let filepath = Sys.argv.(1) in
    let input_cs = chars_from_file filepath in
    let (ts_opt, _) = lex_newick input_cs in
    match ts_opt with
    | None ->
        Printf.eprintf "Lex failure: %s\n%!" filepath;
        exit 1
    | Some ts ->
        let pr = parse_newick ts in
        let meta = {
          parse_result = str_of_coqstr (show_newick_result pr);
          num_tokens   = List.length ts;
          parse_nodes  = fingerprint_newick pr;
          ref_nodes    = None;
        } in
        print_string (metadata_to_json_line meta);
        print_newline ()
  with e ->
    Printf.eprintf "Exception: %s\n%!" (Printexc.to_string e);
    exit 1
