(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Setoid rewriting — Proper instances, generalized rewriting. *)

From Stdlib Require Import Nat Bool List Relations Morphisms.
Import ListNotations.

Module SetoidRw.

(* A simple quotient type: integers mod 3 *)
Definition mod3 (n : nat) : nat := n mod 3.

Definition equiv_mod3 (x y : nat) : Prop := mod3 x = mod3 y.

(* equiv_mod3 is an equivalence relation *)
#[export] Instance equiv_mod3_equiv : Equivalence equiv_mod3.
Proof.
  split.
  - intro x. unfold equiv_mod3. reflexivity.
  - intros x y H. unfold equiv_mod3 in *. symmetry. exact H.
  - intros x y z Hxy Hyz. unfold equiv_mod3 in *.
    transitivity (mod3 y); assumption.
Defined.

(* mod3 is Proper with respect to equiv_mod3 *)
#[export] Instance mod3_proper : Proper (equiv_mod3 ==> eq) mod3.
Proof.
  intros x y H. unfold equiv_mod3 in H. exact H.
Defined.

(* Computational functions *)
Definition classify_mod3 (n : nat) : nat :=
  match mod3 n with
  | 0 => 0
  | 1 => 1
  | _ => 2
  end.

Definition add_mod3 (x y : nat) : nat := mod3 (x + y).

(* Test values *)
Definition test_mod3_0 : nat := mod3 0.
Definition test_mod3_5 : nat := mod3 5.
Definition test_mod3_9 : nat := mod3 9.
Definition test_classify_6 : nat := classify_mod3 6.
Definition test_classify_7 : nat := classify_mod3 7.
Definition test_add_mod3 : nat := add_mod3 5 7.

End SetoidRw.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "setoid_rw" SetoidRw.
