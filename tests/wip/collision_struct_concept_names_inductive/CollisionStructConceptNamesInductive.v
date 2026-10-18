(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Known bug: the child module [List] collides with the [List] struct the
    standard library's [list] is written as, so everything this file
    declares is written inside the struct [CollisionStructConceptNamesInductive],
    and [Keyed]'s concept at the top of the file.  The concept names
    [color], an inductive the file declares, which is a member of the struct
    and so is not declared where the concept is (1 undeclared name).  A type
    alias the concept names, [key], moves out ahead of it and leaves a member
    alias behind; an inductive is never one of the concept's prerequisites
    inside a struct, so it stays. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat List.

Definition key : Set := nat.

Inductive color : Set := Red | Blue.

Class Keyed (A : Set) := { key_of : A -> key; color_of : A -> color }.

Module List.
  Definition first (l : list nat) : nat := match l with nil => 0 | x :: _ => x end.
End List.

#[global] Instance keyed_nat : Keyed nat := {| key_of := fun n => n; color_of := fun _ => Blue |}.

Definition same {A : Set} `{Keyed A} (x y : A) : bool :=
  Nat.eqb (key_of x) (List.first (key_of y :: nil)).

Definition check : bool := same 3 3.

Definition blue : bool := match color_of 3 with Blue => true | Red => false end.

Crane Extraction "collision_struct_concept_names_inductive" check blue.
