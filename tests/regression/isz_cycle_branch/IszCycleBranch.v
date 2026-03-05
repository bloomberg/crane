(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: ISZ cycle count follows post-increment wrap branch. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module IszCycleBranch.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat :=
  nth r (regs s) 0.

Definition nibble_of_nat (n : nat) : nat := n mod 16.

Definition cycles_isz (s : state) (r : nat) : nat :=
  let new_val := nibble_of_nat (get_reg s r + 1) in
  if new_val =? 0 then 8 else 16.

Definition t : nat := cycles_isz (mkState [15]) 0.

End IszCycleBranch.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "isz_cycle_branch" IszCycleBranch.
