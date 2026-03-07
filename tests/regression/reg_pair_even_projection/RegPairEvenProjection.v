(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: even register indices remain their own pair base. *)

From Stdlib Require Import Nat Bool.

Module RegPairEvenProjection.

Definition pair_base (r : nat) : nat := r - r mod 2.

Definition t : bool := Nat.eqb (pair_base 6) 6.

End RegPairEvenProjection.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "reg_pair_even_projection" RegPairEvenProjection.
