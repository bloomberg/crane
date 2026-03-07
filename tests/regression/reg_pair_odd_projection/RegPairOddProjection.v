(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: odd register indices project to the previous even pair base. *)

From Stdlib Require Import Nat Bool.

Module RegPairOddProjection.

Definition pair_base (r : nat) : nat := r - r mod 2.

Definition t : bool := Nat.eqb (pair_base 7) 6.

End RegPairOddProjection.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "reg_pair_odd_projection" RegPairOddProjection.
