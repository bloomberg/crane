(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import ExtrOcamlBasic.
(*Require Import ExtrOcamlNatInt.*)
(*Require Import ExtrOcamlZInt.*)
From Stdlib Require Import ExtrOcamlString.
From Crane.Libraries.ParseALot.Utils Require Import NativeMap.
From Crane.Libraries.ParseALot.Examples.JSON.Parser Require Import JSON.
From Crane.Libraries.ParseALot.Examples.CSV.Parser Require Import CSV.
From Crane.Libraries.ParseALot.Examples.XML.Parser Require Import XML.

Set Extraction Output Directory "extracted".
Extraction Blacklist List String.

(* Extraction anchors. Coq's OCaml extraction only emits a stdlib symbol into its
   home module if some extraction root reaches it at the value/type level. The
   JSON/CSV/XML roots below do not reference [Specif.sigT]/[projT1],
   [Datatypes.option_map]/[sum], or the ordered-set module type [FSetInterface.S]
   directly, so they get pruned -- yet other emitted interfaces (Impl1.mli's
   SemLexerFn, DecimalString.ml, FSetUtil.mli) still mention them, which breaks
   the OCaml build. (The now-deleted PPM/Newick grammars used to force these.)
   These otherwise-unused anchors re-force emission; they add nothing observable
   to the runners. *)
From Stdlib Require Import FSetAVL OrderedTypeEx.
Module AnchorSet := FSetAVL.Make Nat_as_OT.
Definition anchor_set        : AnchorSet.t   := AnchorSet.add 0 AnchorSet.empty.
Definition anchor_sigT       : {_ : nat & nat} := @existT nat (fun _ => nat) 0 0.
Definition anchor_projT1     : nat            := projT1 anchor_sigT.
Definition anchor_option_map : option nat     := option_map (fun n : nat => n) (Some 0).
Definition anchor_sum        : sum nat nat    := inl 0.

(* OCaml realization of the NativeMap axioms (parallel to the Crane C++
   immer::map realization in CraneExtraction.v). Backed by [native_map_impl.ml],
   compiled alongside the extracted code. *)
Extract Constant NativeMap.t "'k" "'v" => "('k, 'v) Native_map_impl.t".
Extract Constant NativeMap.empty => "Native_map_impl.empty".
Extract Constant NativeMap.get => "Native_map_impl.get".
Extract Constant NativeMap.set => "Native_map_impl.set".

Separate Extraction
         lex_json parse_json show_json_result
         lex_csv  parse_csv  show_csv_result
         lex_xml  parse_xml  show_xml_result
         anchor_set anchor_sigT anchor_projT1 anchor_option_map anchor_sum.
