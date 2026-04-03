(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Clock effects for the BDE flavor.

   Re-exports shared definitions from [ClockDefs.v] and adds C++ extraction
   mappings targeting BDE ([bsls::SystemTime]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.ClockDefs.

Crane Extract Inductive clockE => ""
  [ "static_cast<int64_t>(bsls::SystemTime::nowMonotonicClock().totalMilliseconds())"
    "static_cast<int64_t>(bsls::SystemTime::nowRealtimeClock().totalMilliseconds())" ]
  From "bsls_systemtime.h".

Crane Extract Inlined Constant steady_now =>
  "static_cast<int64_t>(bsls::SystemTime::nowMonotonicClock().totalMilliseconds())"
  From "bsls_systemtime.h".
Crane Extract Inlined Constant system_now =>
  "static_cast<int64_t>(bsls::SystemTime::nowRealtimeClock().totalMilliseconds())"
  From "bsls_systemtime.h".
Crane Extract Inlined Constant now =>
  "static_cast<int64_t>(bsls::SystemTime::nowRealtimeClock().totalMilliseconds())"
  From "bsls_systemtime.h".
