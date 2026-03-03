(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Opaque (Qed) vs Transparent (Defined) definitions. *)

From Stdlib Require Import Nat Bool List Lia.
Import ListNotations.

Module Opaque.

(* === Transparent proof (Defined) — should be extractable === *)

Definition safe_pred (n : nat) (H : n > 0) : nat.
Proof.
  destruct n.
  - exfalso. inversion H.
  - exact n.
Defined.

(* === Opaque proof (Qed) — should be erased === *)

Lemma succ_gt_zero : forall n, S n > 0.
Proof.
  intros. lia.
Qed.

(* === Function using transparent proof === *)

Definition pred_of_succ (n : nat) : nat :=
  safe_pred (S n) (succ_gt_zero n).

(* === Transparent decision procedure === *)

Definition nat_eq_dec (n m : nat) : {n = m} + {n <> m}.
Proof.
  decide equality.
Defined.

Definition are_equal (n m : nat) : bool :=
  if nat_eq_dec n m then true else false.

(* === Sig type with transparent projection === *)

Definition bounded_add (a b : nat) (bound : nat)
  : {n : nat | n <= bound + bound}.
Proof.
  exists (a + b).
  (* We don't prove this properly, just admit for extraction testing *)
  admit.
Admitted.

(* === Test values === *)

Definition test_safe_pred : nat := safe_pred 5 (succ_gt_zero 4).
Definition test_pred_succ : nat := pred_of_succ 7.
Definition test_eq_true : bool := are_equal 5 5.
Definition test_eq_false : bool := are_equal 3 7.

End Opaque.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "opaque" Opaque.
