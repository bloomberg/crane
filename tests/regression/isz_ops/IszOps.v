(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged ISZ operation tests: cycle branching, iteration counting, and loop flags. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module IszOps.

(* Shared state and utilities *)
Definition nibble_of_nat (n : nat) : nat := n mod 16.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat :=
  nth r (regs s) 0.

(* ISZ cycle count branching *)
Definition cycles_isz (s : state) (r : nat) : nat :=
  let new_val := nibble_of_nat (get_reg s r + 1) in
  if new_val =? 0 then 8 else 16.

Definition test_cycle_branch : nat :=
  cycles_isz (mkState [15]) 0.

(* ISZ iterations remaining *)
Definition isz_iterations (v : nat) : nat :=
  if v =? 0 then 16 else 16 - v.

Definition test_iterations_remaining : nat :=
  isz_iterations 0 + isz_iterations 12.

(* ISZ loop flags *)
Definition isz_loops (s : state) (r : nat) : bool :=
  negb (nibble_of_nat (get_reg s r + 1) =? 0).

Definition isz_terminates (s : state) (r : nat) : bool :=
  nibble_of_nat (get_reg s r + 1) =? 0.

Definition test_loop_flags : nat :=
  let s := mkState [15; 3] in
  (if isz_loops s 0 then 1 else 0) +
  (if isz_terminates s 0 then 1 else 0).

(* Combined test result as tuple *)
Definition t : nat * nat * nat :=
  (test_cycle_branch, test_iterations_remaining, test_loop_flags).

End IszOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "isz_ops" IszOps.
