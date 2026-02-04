(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test higher-order functions *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module HigherOrder.

(* Simple list *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* Map: apply function to each element *)
Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

(* Fold right *)
Fixpoint foldr {A B : Type} (f : A -> B -> B) (z : B) (l : list A) : B :=
  match l with
  | nil => z
  | cons x xs => f x (foldr f z xs)
  end.

(* Fold left *)
Fixpoint foldl {A B : Type} (f : B -> A -> B) (z : B) (l : list A) : B :=
  match l with
  | nil => z
  | cons x xs => foldl f (f z x) xs
  end.

(* Function composition *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

(* Apply function n times *)
Fixpoint iterate {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S m => f (iterate m f x)
  end.

(* Function that returns a function *)
Definition adder (n : nat) : nat -> nat := fun m => Nat.add n m.

(* Function that takes a function and returns a function *)
Definition twice {A : Type} (f : A -> A) : A -> A := fun x => f (f x).

(* Pipeline operator simulation *)
Definition pipe {A B : Type} (x : A) (f : A -> B) : B := f x.

(* Test list *)
Definition test_list : list nat := cons one (cons two (cons three (cons four (cons five nil)))).

(* Test values *)
Definition test_map := foldr Nat.add zero (map (Nat.add one) test_list).
Definition test_foldr := foldr Nat.add zero test_list.
Definition test_foldl := foldl Nat.add zero test_list.
Definition test_compose := compose (Nat.mul two) (Nat.add one) three.
Definition test_iterate := iterate three (Nat.add two) zero.
Definition test_adder := adder five three.
Definition test_twice := twice (Nat.add one) five.
Definition test_pipe := pipe five (adder three).

End HigherOrder.

Crane Extraction "higher_order" HigherOrder.
