(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JIN combines the next-page base with a register-pair offset. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module JinUsesPairForJump.

Record state : Type := mkState {
  regs : list nat;
  pc : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition page_of (addr : nat) : nat := addr / 256.

Definition execute_jin (s : state) (r : nat) : state :=
  let next_page := page_of (pc s + 1) in
  let pair_val := get_reg_pair s r in
  mkState (regs s) (next_page * 256 + pair_val mod 256).

Definition sample : state := mkState [0; 0; 2; 11; 0; 0] 300.
Definition t : bool := Nat.eqb (pc (execute_jin sample 3)) 555.

End JinUsesPairForJump.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "jin_uses_pair_for_jump" JinUsesPairForJump.
