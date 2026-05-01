(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Extraction wrapper: re-imports the spreadsheet model from
   theories/Examples/Spreadsheet and emits Spreadsheet.h / Spreadsheet.cpp
   into this directory (via the dune coq.theory's -output-directory flag).
*)
From Crane.Examples.Spreadsheet Require Import Spreadsheet.
Require Crane.Extraction.

Crane Extraction "Spreadsheet" Spreadsheet.
