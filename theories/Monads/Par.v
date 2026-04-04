(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Parallel computation effects for the standard library flavor.

   Re-exports shared definitions from [ParDefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.ParDefs.

Crane Extract Inductive parE => ""
  [ "std::async(std::launch::async, %a0, %a1)" "%a0.get()" ].

Crane Extract Inlined Constant future => "std::future<%t0>" From "future".
Crane Extract Inlined Constant async =>
  "std::async(std::launch::async, %a0, %a1)".
