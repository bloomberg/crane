(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: SRC decomposes the selected register pair into ROM and RAM selectors. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SrcUsesPairValue.

Record state : Type := mkState {
  regs : list nat;
  sel_rom : nat;
  sel_chip : nat;
  sel_reg : nat;
  sel_char : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition execute_src (s : state) (r : nat) : state :=
  let pair_val := get_reg_pair s r in
  let hi := pair_val / 16 in
  mkState (regs s) hi (hi / 4) (hi mod 4) (pair_val mod 16).

Definition sample : state := mkState [0; 0; 1; 11; 0; 0] 0 0 0 0.
Definition after : state := execute_src sample 3.
Definition t : bool :=
  andb
    (Nat.eqb (sel_rom after) 1)
    (andb
      (Nat.eqb (sel_chip after) 0)
      (andb (Nat.eqb (sel_reg after) 1)
            (Nat.eqb (sel_char after) 11))).

End SrcUsesPairValue.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "src_uses_pair_value" SrcUsesPairValue.
