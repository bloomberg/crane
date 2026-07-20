(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression harness for the Real floor guard (theories/cpp/crane_real.h).
   The Rocq side only forces the generated header to include <crane_real.h>;
   the actual checks (NaN / infinity / out-of-range doubles do not invoke
   undefined behaviour when floored to int64_t) live in
   real_floor_guard.t.cpp, which drives the shipped [r_floor_z] helper
   directly. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Real.
From Stdlib Require Import Reals.

Module RealFloorGuard.
Definition anchor : R := R0.
End RealFloorGuard.

Crane Extraction "real_floor_guard" RealFloorGuard.
