(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Clock effects for the standard library flavor.

   Re-exports shared definitions from [ClockDefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::chrono]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.ClockDefs.

Crane Extract Inductive clockE => ""
  [ "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count())"
    "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count())" ]
  From "chrono".

Crane Extract Inlined Constant steady_now =>
  "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count())"
  From "chrono".
Crane Extract Inlined Constant system_now =>
  "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count())"
  From "chrono".
Crane Extract Inlined Constant now =>
  "static_cast<int64_t>(std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count())"
  From "chrono".
