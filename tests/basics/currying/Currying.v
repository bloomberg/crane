(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test currying and partial application *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module Currying.

(* Multi-argument function (curried) *)
Definition add3 (a b c : nat) : nat := Nat.add a (Nat.add b c).

(* Partial application - apply one argument *)
Definition add3_partial1 : nat -> nat -> nat := add3 one.

(* Partial application - apply two arguments *)
Definition add3_partial2 : nat -> nat := add3 one two.

(* Explicit curry/uncurry *)
Inductive pair (A B : Type) : Type :=
| Pair : A -> B -> pair A B.

Arguments Pair {A B} _ _.

Definition curry {A B C : Type} (f : pair A B -> C) : A -> B -> C :=
  fun a b => f (Pair a b).

Definition uncurry {A B C : Type} (f : A -> B -> C) : pair A B -> C :=
  fun p => match p with Pair a b => f a b end.

(* Test curry/uncurry *)
Definition pair_add (p : pair nat nat) : nat :=
  match p with Pair a b => Nat.add a b end.

Definition curried_add : nat -> nat -> nat := curry pair_add.
Definition uncurried_add3 : pair nat (pair nat nat) -> nat :=
  fun p => match p with Pair a bc =>
    match bc with Pair b c => add3 a b c end
  end.

(* Flip argument order *)
Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Definition sub (a b : nat) : nat := Nat.sub a b.
Definition flipped_sub : nat -> nat -> nat := flip sub.

(* Section with partial application *)
Section WithBase.
  Variable base : nat.
  Definition add_base (n : nat) : nat := Nat.add base n.
End WithBase.

(* After section, base becomes a parameter *)
Definition add_ten : nat -> nat := add_base (Nat.mul two five).

(* Test values *)
Definition test_add3 := add3 one two three.
Definition test_partial1 := add3_partial1 two three.
Definition test_partial2 := add3_partial2 three.
Definition test_curried := curried_add three four.
Definition test_flip := flipped_sub three seven.
Definition test_add_ten := add_ten five.

End Currying.

Crane Extraction "currying" Currying.
