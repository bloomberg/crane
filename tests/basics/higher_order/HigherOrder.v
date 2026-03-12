(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test higher-order functions *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module HigherOrder.

(** A simple polymorphic list type. *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(** [map f l] applies [f] to each element of [l], producing a new list. *)
Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

(** [foldr f z l] folds [l] from the right using [f] with initial
    accumulator [z]. *)
Fixpoint foldr {A B : Type} (f : A -> B -> B) (z : B) (l : list A) : B :=
  match l with
  | nil => z
  | cons x xs => f x (foldr f z xs)
  end.

(** [foldl f z l] folds [l] from the left using [f] with initial
    accumulator [z]. This is tail-recursive. *)
Fixpoint foldl {A B : Type} (f : B -> A -> B) (z : B) (l : list A) : B :=
  match l with
  | nil => z
  | cons x xs => foldl f (f z x) xs
  end.

(** [compose g f] returns the composition of [g] after [f]. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

(** [iterate n f x] applies [f] to [x] a total of [n] times. *)
Fixpoint iterate {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S m => f (iterate m f x)
  end.

(** [adder n] returns a function that adds [n] to its argument. *)
Definition adder (n : nat) : nat -> nat := fun m => Nat.add n m.

(** [twice f] returns a function that applies [f] two times. *)
Definition twice {A : Type} (f : A -> A) : A -> A := fun x => f (f x).

(** [pipe x f] applies [f] to [x], simulating a pipeline operator. *)
Definition pipe {A B : Type} (x : A) (f : A -> B) : B := f x.

(* Test list *)
Definition test_list : list nat := cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))).

(* Test values *)
Definition test_map := foldr Nat.add 0 (map (Nat.add 1) test_list).
Definition test_foldr := foldr Nat.add 0 test_list.
Definition test_foldl := foldl Nat.add 0 test_list.
Definition test_compose := compose (Nat.mul 2) (Nat.add 1) 3.
Definition test_iterate := iterate 3 (Nat.add 2) 0.
Definition test_adder := adder 5 3.
Definition test_twice := twice (Nat.add 1) 5.
Definition test_pipe := pipe 5 (adder 3).

End HigherOrder.

Crane Extraction "higher_order" HigherOrder.
