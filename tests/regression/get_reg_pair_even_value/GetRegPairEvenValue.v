(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: get_reg_pair combines adjacent register nibbles into a byte. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module GetRegPairEvenValue.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition t : nat := get_reg_pair (mkState [0; 1; 10; 11]) 2.

End GetRegPairEvenValue.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "get_reg_pair_even_value" GetRegPairEvenValue.
