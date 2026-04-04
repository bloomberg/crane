(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrency effects for the standard library flavor.

   Re-exports shared definitions from [ThreadDefs.v] and adds C++
   extraction mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.IO.
From Crane Require Export Monads.ThreadDefs.

Crane Extract Inductive threadE => ""
  [ "%a0.join()"
    "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))" ]
  From "thread" "chrono".

Crane Extract Inlined Constant thread => "std::thread" From "thread".
Crane Extract Inlined Constant spawn => "std::thread(%a0, %a1)" From "thread".
Crane Extract Inlined Constant sleep =>
  "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))"
  From "thread" "chrono".
