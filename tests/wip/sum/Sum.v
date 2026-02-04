(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test extraction of sum types *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module Sum.

(* Define a simple sum type (Either) *)
Inductive either (A B : Type) : Type :=
| Left : A -> either A B
| Right : B -> either A B.

Arguments Left {A B} _.
Arguments Right {A B} _.

(* Test sum type construction *)
Definition left_val : either nat bool := Left five.
Definition right_val : either nat bool := Right true.

(* Test pattern matching on sum types *)
Definition either_to_nat (e : either nat nat) : nat :=
  match e with
  | Left n => n
  | Right m => m
  end.

(* Test with different types on each side *)
Definition is_left {A B : Type} (e : either A B) : bool :=
  match e with
  | Left _ => true
  | Right _ => false
  end.

(* Test mapping over either *)
Definition map_left {A B C : Type} (f : A -> C) (e : either A B) : either C B :=
  match e with
  | Left a => Left (f a)
  | Right b => Right b
  end.

Definition map_right {A B C : Type} (f : B -> C) (e : either A B) : either A C :=
  match e with
  | Left a => Left a
  | Right b => Right (f b)
  end.

(* Triple sum type *)
Inductive triple (A B C : Type) : Type :=
| First : A -> triple A B C
| Second : B -> triple A B C
| Third : C -> triple A B C.

Arguments First {A B C} _.
Arguments Second {A B C} _.
Arguments Third {A B C} _.

Definition triple_test : triple nat bool nat := Second true.

(* Test values *)
Definition test_left := is_left left_val.
Definition test_right := is_left right_val.
Definition test_either := either_to_nat (Left three).

End Sum.

Crane Extraction "sum" Sum.
