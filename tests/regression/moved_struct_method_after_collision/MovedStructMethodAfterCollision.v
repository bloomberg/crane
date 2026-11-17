(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The child module [List] collides with the [List] struct the standard
    library's [list] is written as, so everything this file declares is
    written inside the struct [MovedStructMethodAfterCollision], and
    [Shaped]'s concept at the top of the file.  The concept names [shape],
    which moves out of the struct ahead of the concept.  Its method [size]
    calls [Helpers.inc], a member of the struct, which is not declared
    where [shape] now is: [size] is declared in [shape] and defined after
    the struct, as a method of a struct at namespace scope naming a
    module's struct is. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat List.

Module Helpers.
  Definition inc (n : nat) : nat := S n.
End Helpers.

Inductive shape : Set := Circle (r : nat) | Square (s : nat) (t : shape).

Fixpoint size (x : shape) : nat := match x with Circle r => Helpers.inc r | Square s t => s + size t end.

Class Shaped (A : Set) := { shape_of : A -> shape }.

Module List.
  Definition first (l : list nat) : nat := match l with nil => 0 | x :: _ => x end.
End List.

#[global] Instance shaped_nat : Shaped nat := {| shape_of := fun n => Square n (Circle n) |}.

Definition sz : nat := size (shape_of 3).

Definition head_or_zero (l : list nat) : nat := List.first l.

Crane Extraction "moved_struct_method_after_collision" sz head_or_zero.
