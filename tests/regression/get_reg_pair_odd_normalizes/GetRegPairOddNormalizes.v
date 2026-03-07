(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: odd register indices normalize to the same pair as the previous even index. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module GetRegPairOddNormalizes.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition t : bool := Nat.eqb (get_reg_pair (mkState [0; 1; 10; 11]) 2)
                              (get_reg_pair (mkState [0; 1; 10; 11]) 3).

End GetRegPairOddNormalizes.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "get_reg_pair_odd_normalizes" GetRegPairOddNormalizes.
