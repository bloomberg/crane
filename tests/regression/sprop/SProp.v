(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: SProp — strict propositions (proof irrelevance). *)

From Stdlib Require Import Nat Bool.

Module SPropTest.

(* === SProp type === *)

Inductive sTrue : SProp := sI.
Inductive sFalse : SProp := .

Inductive sAnd (A B : SProp) : SProp :=
  sconj : A -> B -> sAnd A B.

(* === Squash: erase any Prop to SProp === *)

Inductive Squash (A : Type) : SProp :=
  squash : A -> Squash A.

(* === Box: computationally relevant wrapper with SProp proof === *)

Record Box (P : SProp) (A : Type) := mkBox {
  box_proof : P;
  box_value : A
}.

Arguments mkBox {P A} _ _.
Arguments box_value {P A} _.

(* === Functions that carry SProp witnesses === *)

Definition guarded_pred (n : nat) (pf : sTrue) : nat :=
  match n with
  | 0 => 0
  | S m => m
  end.

Definition safe_div (a b : nat) (pf : sTrue) : nat :=
  Nat.div a b.

(* === Test values === *)

Definition test_guarded : nat := guarded_pred 5 sI.
Definition test_box : nat := box_value (mkBox sI 42).
Definition test_div : nat := safe_div 10 3 sI.

End SPropTest.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "sprop" SPropTest.
