(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The child module [List] collides with the [List] struct the standard
    library's [list] is written as, so everything this file declares is
    written inside the struct [CollisionStructConceptNamesInductive], and
    [Keyed]'s concept at the top of the file.  The concept names [key], a
    type alias, and [color], an inductive written as an enum, both members of
    the struct, so neither was declared where the concept is.  Each moves out
    ahead of the concept and leaves a member alias behind, through which the
    struct still names it: both are spelled bare, wherever they are.  An
    inductive written as a struct is spelled qualified by the struct, and
    does not move (wip collision_struct_concept_names_struct). *)

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
