(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined regression tests for register pair operations. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RegisterPair.

(* Shared helper functions *)
Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState { regs : list nat }.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition set_reg (s : state) (r v : nat) : state :=
  mkState (update_nth r (v mod 16) (regs s)).

Definition pair_base (r : nat) : nat := r - r mod 2.

Definition set_reg_pair (s : state) (r v : nat) : state :=
  let base := r - r mod 2 in
  let hi := v / 16 in
  let lo := v mod 16 in
  let s1 := set_reg s base hi in
  set_reg s1 (base + 1) lo.

Definition sample : state := mkState [0; 0; 0; 0; 0; 0].

(* Test 1: even register indices remain their own pair base *)
Definition even_projection : bool := Nat.eqb (pair_base 6) 6.

(* Test 2: odd register indices project to the previous even pair base *)
Definition odd_projection : bool := Nat.eqb (pair_base 7) 6.

(* Test 3: setting a register pair exposes the high nibble through get_reg *)
Definition set_pair_get_high : bool := Nat.eqb (get_reg (set_reg_pair sample 2 171) 2) 10.

(* Test 4: setting a register pair exposes the low nibble through get_reg *)
Definition set_pair_get_low : bool := Nat.eqb (get_reg (set_reg_pair sample 2 171) 3) 11.

End RegisterPair.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "register_pair" RegisterPair.
