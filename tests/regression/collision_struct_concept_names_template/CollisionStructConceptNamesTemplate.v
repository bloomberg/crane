(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The child module [List] collides with the [List] struct the standard
    library's [list] is written as, so everything this file declares is
    written inside the struct [CollisionStructConceptNamesTemplate], and
    [Shaped]'s concept at the top of the file.  The concept names [shape]
    and the template [box], which move out of the struct ahead of the
    concept, and [color], which [shape] holds by value, moves with them.
    Each leaves a member alias behind, [box]'s a template over its
    parameter. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat List.

Definition helper (n : nat) : nat := n + 1.

Inductive color : Set := Red (k : nat) | Mix (a b : color).

Inductive shape : Set := Circle (r : nat) (c : color) | Square (s : nat) (t : shape).

Fixpoint size (x : shape) : nat := match x with Circle r _ => helper r | Square s t => s + size t end.

Inductive box (A : Set) : Set := Box (a : A) (s : shape).
Arguments Box {A}.

Class Shaped (A : Set) := { shape_of : A -> shape; boxed : A -> box A }.

Module List.
  Definition first (l : list nat) : nat := match l with nil => 0 | x :: _ => x end.
End List.

#[global] Instance shaped_nat : Shaped nat :=
  {| shape_of := fun n => Square n (Circle n (Red n)); boxed := fun n => Box n (Circle n (Red 0)) |}.

Definition sz : nat := size (shape_of 3).

Definition bx : nat := match boxed 2 with Box a s => a + size s end.

Definition head_or_zero (l : list nat) : nat := List.first l.

Crane Extraction "collision_struct_concept_names_template" sz bx head_or_zero.
