(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged regression tests for register pair operations. *)

From Stdlib Require Import List Nat Bool Arith.PeanoNat.
Import ListNotations.

Module RegisterPairOps.

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

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition set_reg_pair (s : state) (r v : nat) : state :=
  let base := r - r mod 2 in
  let hi := v / 16 in
  let lo := v mod 16 in
  let s1 := set_reg s base hi in
  set_reg s1 (base + 1) lo.

(* Test 1: get_reg_pair_even_value *)
(* get_reg_pair combines adjacent register nibbles into a byte *)
Definition test_get_reg_pair_even_value : nat :=
  get_reg_pair (mkState [0; 1; 10; 11]) 2.

(* Test 2: get_reg_pair_from_regs *)
(* get_reg_pair reconstructs a byte from two adjacent registers *)
Definition sample_from_regs : state := mkState [0; 0; 10; 11; 0; 0].
Definition test_get_reg_pair_from_regs : bool :=
  Nat.eqb (get_reg_pair sample_from_regs 2) 171.

(* Test 3: get_reg_pair_odd_normalizes *)
(* odd register indices normalize to the same pair as the previous even index *)
Definition test_get_reg_pair_odd_normalizes : bool :=
  Nat.eqb (get_reg_pair (mkState [0; 1; 10; 11]) 2)
          (get_reg_pair (mkState [0; 1; 10; 11]) 3).

(* Test 4: set_reg_affects_pair_high *)
(* setting an even register changes the high nibble of its pair *)
Definition sample_pair_high : state := mkState [2; 9; 4; 7; 8; 1].
Definition test_set_reg_affects_pair_high : bool :=
  Nat.eqb (get_reg_pair (set_reg sample_pair_high 2 13) 2)
          (13 * 16 + get_reg sample_pair_high 3).

(* Test 5: set_reg_affects_pair_low *)
(* setting an odd register changes the low nibble of its pair *)
Definition sample_pair_low : state := mkState [2; 9; 4; 7; 8; 1].
Definition test_set_reg_affects_pair_low : bool :=
  Nat.eqb (get_reg_pair (set_reg sample_pair_low 3 12) 3)
          (get_reg sample_pair_low 2 * 16 + 12).

(* Test 6: set_reg_pair_idempotent *)
(* setting the same register pair twice keeps the final value *)
Definition sample_idempotent : state := mkState [0; 0; 0; 0; 0; 0].
Definition test_set_reg_pair_idempotent : bool :=
  Nat.eqb
    (get_reg_pair (set_reg_pair (set_reg_pair sample_idempotent 2 34) 2 171) 2)
    171.

(* Test 7: set_reg_pair_preserves_other_pairs *)
(* setting one register pair leaves another pair unchanged *)
Definition sample_preserves : state := mkState [1; 2; 3; 4; 5; 6].
Definition test_set_reg_pair_preserves_other_pairs : bool :=
  Nat.eqb
    (get_reg_pair (set_reg_pair sample_preserves 0 171) 2)
    (get_reg_pair sample_preserves 2).

(* Test 8: register_pair *)
(* Combined tests from register_pair *)
Definition pair_base (r : nat) : nat := r - r mod 2.

Definition sample_register_pair : state := mkState [0; 0; 0; 0; 0; 0].

(* even register indices remain their own pair base *)
Definition test_even_projection : bool := Nat.eqb (pair_base 6) 6.

(* odd register indices project to the previous even pair base *)
Definition test_odd_projection : bool := Nat.eqb (pair_base 7) 6.

(* setting a register pair exposes the high nibble through get_reg *)
Definition test_set_pair_get_high : bool :=
  Nat.eqb (get_reg (set_reg_pair sample_register_pair 2 171) 2) 10.

(* setting a register pair exposes the low nibble through get_reg *)
Definition test_set_pair_get_low : bool :=
  Nat.eqb (get_reg (set_reg_pair sample_register_pair 2 171) 3) 11.

(* Test 9: register_pair_architecture *)
(* each register index maps to one of the eight register pairs *)
Definition pair_index (r : nat) : nat := r / 2.

Definition pair_property (r : nat) : bool :=
  let p := pair_index r in
  andb (Nat.ltb p 8)
       (orb (Nat.eqb r (2 * p))
            (Nat.eqb r (2 * p + 1))).

Definition test_regs : list nat := seq 0 16.

Definition test_register_pair_architecture : bool := forallb pair_property test_regs.

(* Test 10: register_pair_even_rounding *)
(* register-pair access with even-index rounding *)
Definition sample_even_rounding : state := mkState [0; 1; 2; 3; 4; 5].
Definition test_register_pair_even_rounding : nat :=
  get_reg_pair (set_reg_pair sample_even_rounding 3 45) 3.

(* Test 11: reg_pair_successor *)
(* even/odd registers index the same pair as successor/predecessor *)
Definition sample_successor : state := mkState [0; 0; 10; 11; 0; 0].

(* Even register indexes the same pair as its successor *)
Definition test_even_same_as_successor : bool :=
  Nat.eqb (get_reg_pair sample_successor 2) (get_reg_pair sample_successor 3).

(* Odd register indexes the same pair as its predecessor *)
Definition test_odd_same_as_predecessor : bool :=
  Nat.eqb (get_reg_pair sample_successor 3) (get_reg_pair sample_successor 2).

Definition test_reg_pair_successor : bool :=
  test_even_same_as_successor && test_odd_same_as_predecessor.

(* Combined result: tuple of all test values *)
Definition t : (nat * bool * bool * bool * bool * bool * bool * bool * bool * bool * bool * bool * nat * bool) :=
  (test_get_reg_pair_even_value,
   test_get_reg_pair_from_regs,
   test_get_reg_pair_odd_normalizes,
   test_set_reg_affects_pair_high,
   test_set_reg_affects_pair_low,
   test_set_reg_pair_idempotent,
   test_set_reg_pair_preserves_other_pairs,
   test_even_projection,
   test_odd_projection,
   test_set_pair_get_high,
   test_set_pair_get_low,
   test_register_pair_architecture,
   test_register_pair_even_rounding,
   test_reg_pair_successor).

End RegisterPairOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "register_pair_ops" RegisterPairOps.
