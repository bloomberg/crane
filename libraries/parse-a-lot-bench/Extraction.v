(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import ExtrOcamlBasic.
(*Require Import ExtrOcamlNatInt.*)
(*Require Import ExtrOcamlZInt.*)
From Stdlib Require Import ExtrOcamlString.
From Crane.Libraries.ParseALot.Utils Require Import NativeMap.
From Crane.Libraries.ParseALot.Examples.PPM.Parser Require Import PPM.
From Crane.Libraries.ParseALot.Examples.JSON.Parser Require Import JSON.
From Crane.Libraries.ParseALot.Examples.Newick.Parser Require Import Newick.
From Crane.Libraries.ParseALot.Examples.XML.Parser Require Import XML.

Set Extraction Output Directory "extracted".
Extraction Blacklist List String.

(* OCaml realization of the NativeMap axioms (parallel to the Crane C++
   immer::map realization in CraneExtraction.v). Backed by [native_map_impl.ml],
   compiled alongside the extracted code. *)
Extract Constant NativeMap.t "'k" "'v" => "('k, 'v) Native_map_impl.t".
Extract Constant NativeMap.empty => "Native_map_impl.empty".
Extract Constant NativeMap.get => "Native_map_impl.get".
Extract Constant NativeMap.set => "Native_map_impl.set".

Separate Extraction
         lex_ppm    parse_ppm    show_ppm_result
         lex_json   parse_json   show_json_result
         lex_newick parse_newick show_newick_result
         lex_xml    parse_xml    show_xml_result.
