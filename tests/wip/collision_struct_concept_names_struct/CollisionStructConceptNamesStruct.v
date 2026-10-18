(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Known bug: the child module [List] collides with the [List] struct the
    standard library's [list] is written as, so everything this file
    declares is written inside the struct [CollisionStructConceptNamesStruct],
    and [Shaped]'s concept at the top of the file.  The concept names
    [shape], an inductive written as a struct, which is a member of that
    struct, spelled [CollisionStructConceptNamesStruct::Shape] by every
    reference, the concept's included, and so is not declared where the
    concept is (1 undeclared name).  An alias or an enum the concept names
    moves out ahead of it and leaves a member alias behind, because each is
    spelled bare; moving this struct would also have to respell every
    reference to it, its own body's and the concept's among them, and its
    out-of-line members' qualifiers. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat List.

Inductive shape : Set := Circle (r : nat) | Square (s : nat) (t : shape).

Fixpoint size (x : shape) : nat := match x with Circle r => r | Square s t => s + size t end.

Class Shaped (A : Set) := { shape_of : A -> shape }.

Module List.
  Definition first (l : list nat) : nat := match l with nil => 0 | x :: _ => x end.
End List.

#[global] Instance shaped_nat : Shaped nat := {| shape_of := fun n => Square n (Circle n) |}.

Definition sz : nat := size (shape_of 3).

Definition head_or_zero (l : list nat) : nat := List.first l.

Crane Extraction "collision_struct_concept_names_struct" sz head_or_zero.
