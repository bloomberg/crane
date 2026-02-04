(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test implicit arguments *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module ImplicitArgs.

(* Simple implicit type argument *)
Definition id {A : Type} (x : A) : A := x.

(* Multiple implicit arguments *)
Definition fst_of {A B : Type} (x : A) (y : B) : A := x.

(* Implicit argument in the middle *)
Definition apply {A B : Type} (f : A -> B) (x : A) : B := f x.

(* Chained implicits *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C :=
  g (f x).

(* Simple list for testing *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A} _ _.

(* Implicit in inductive pattern match *)
Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => zero
  | mycons _ rest => Nat.add one (length rest)
  end.

(* Using @ to provide implicit arguments explicitly *)
Definition explicit_id := @id nat five.
Definition explicit_fst := @fst_of nat bool three true.

(* Partial application with implicits *)
Definition add_one := Nat.add one.
Definition double_nat (n : nat) := Nat.add n n.

(* Test values *)
Definition test_id := id five.
Definition test_fst := fst_of three seven.
Definition test_apply := apply double_nat five.
Definition test_compose := compose double_nat (Nat.add one) three.
Definition test_length := length (mycons one (mycons two (mycons three mynil))).
Definition test_explicit_id := explicit_id.
Definition test_explicit_fst := explicit_fst.

End ImplicitArgs.

Crane Extraction "implicit_args" ImplicitArgs.
