(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: remaining ISZ iteration count function. *)

From Stdlib Require Import Nat.

Module IszIterationsRemaining.

Definition isz_iterations (v : nat) : nat :=
  if v =? 0 then 16 else 16 - v.

Definition t : nat :=
  isz_iterations 0 + isz_iterations 12.

End IszIterationsRemaining.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "isz_iterations_remaining" IszIterationsRemaining.
