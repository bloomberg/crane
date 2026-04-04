(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Parallel computation effects for the BDE flavor.

   Re-exports shared definitions from [ParDefs.v] and adds C++ extraction
   mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.ParDefs.

Crane Extract Inductive parE => ""
  [ "bsl::async(bsl::launch::async, %a0, %a1)" "%a0.get()" ]
  From "bsl_future.h".

Crane Extract Inlined Constant future => "bsl::future<%t0>" From "bsl_future.h".
Crane Extract Inlined Constant async =>
  "bsl::async(bsl::launch::async, %a0, %a1)" From "bsl_future.h".
