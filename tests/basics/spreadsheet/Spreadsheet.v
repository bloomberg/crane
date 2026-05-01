(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: spreadsheet kernel — re-extracts the model under the
   lowercase output name so the dune test rule picks up
   spreadsheet.{h,cpp}. *)
From Crane.Examples.Spreadsheet Require Import Spreadsheet.
Require Crane.Extraction.

Crane Extraction "spreadsheet" Spreadsheet.
