(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Concurrency effects for the BDE flavor.

   Re-exports shared definitions from [ThreadDefs.v] and adds C++
   extraction mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.IOBDE.
From Crane Require Export Monads.ThreadDefs.

Crane Extract Inductive threadE => ""
  [ "%a0.join()"
    "bsl::this_thread::sleep_for(std::chrono::milliseconds(%a0))" ]
  From "bsl_thread.h" "chrono".

Crane Extract Inlined Constant thread => "bsl::thread" From "bsl_thread.h".
Crane Extract Inlined Constant spawn => "bsl::thread(%a0, %a1)" From "bsl_thread.h".
Crane Extract Inlined Constant sleep =>
  "bsl::this_thread::sleep_for(std::chrono::milliseconds(%a0))"
  From "bsl_thread.h" "chrono".
