(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Mutual coinductive types. *)

From Stdlib Require Import Nat List.
Import ListNotations.

Module MutualCoind.

(* === Mutual coinductive: alternating streams === *)

CoInductive streamA (A : Type) : Type :=
  | consA : A -> streamB A -> streamA A
with streamB (A : Type) : Type :=
  | consB : A -> streamA A -> streamB A.

Arguments consA {A} _ _.
Arguments consB {A} _ _.

(* === Accessors === *)

Definition headA {A : Type} (s : streamA A) : A :=
  match s with consA x _ => x end.

Definition tailA {A : Type} (s : streamA A) : streamB A :=
  match s with consA _ t => t end.

Definition headB {A : Type} (s : streamB A) : A :=
  match s with consB x _ => x end.

Definition tailB {A : Type} (s : streamB A) : streamA A :=
  match s with consB _ t => t end.

(* === Corecursive constructors === *)

CoFixpoint countA (n : nat) : streamA nat :=
  consA n (countB (S n))
with countB (n : nat) : streamB nat :=
  consB n (countA (S n)).

(* === Fuel-based prefix extraction === *)

Fixpoint takeA {A : Type} (fuel : nat) (s : streamA A) : list A :=
  match fuel with
  | 0 => []
  | S f => match s with consA x t => x :: takeB f t end
  end
with takeB {A : Type} (fuel : nat) (s : streamB A) : list A :=
  match fuel with
  | 0 => []
  | S f => match s with consB x t => x :: takeA f t end
  end.

(* === Test values === *)

Definition test_headA : nat := headA (countA 0).
Definition test_headB : nat := headB (countB 10).
Definition test_take5 : list nat := takeA 5 (countA 0).

End MutualCoind.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "mutual_coind" MutualCoind.
