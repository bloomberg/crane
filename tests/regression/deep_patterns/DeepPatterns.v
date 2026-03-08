(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Deeply nested pattern matching - comprehensive test suite. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module DeepPatterns.

(* Deep match on nested options *)
Definition deep_option (x : option (option (option nat))) : nat :=
  match x with
  | Some (Some (Some n)) => n
  | Some (Some None) => 1
  | Some None => 2
  | None => 3
  end.

(* Deep match on nested pairs *)
Definition deep_pair (p : (nat * nat) * (nat * nat)) : nat :=
  match p with
  | ((a, b), (c, d)) => a + b + c + d
  end.

(* Deep match on list structure *)
Definition list_shape (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | [x; y] => x + y
  | [x; y; z] => x + y + z
  | x :: y :: z :: _ :: rest => x + y + z + length rest
  end.

(* Deep match on nested sum types *)
Inductive outer :=
  | OLeft : inner -> outer
  | ORight : nat -> outer
with inner :=
  | ILeft : nat -> inner
  | IRight : bool -> inner.

Definition deep_sum (o : outer) : nat :=
  match o with
  | OLeft (ILeft n) => n
  | OLeft (IRight true) => 1
  | OLeft (IRight false) => 0
  | ORight n => n + 100
  end.

(* Deep match mixing constructors *)
Definition complex_match (x : option (nat * list nat)) : nat :=
  match x with
  | None => 0
  | Some (n, []) => n
  | Some (n, [m]) => n + m
  | Some (n, m :: _ :: rest) => n + m + length rest
  end.

(* Nested match with guards via if *)
Definition guarded_match (p : nat * nat) : nat :=
  match p with
  | (a, b) => if Nat.leb a b then b - a else a - b
  end.

(* Additional patterns from deep_match test *)

(* Simple custom pair type for additional coverage *)
Inductive pair (A B : Type) : Type :=
| Pair : A -> B -> pair A B.

Arguments Pair {A B} _ _.

(* Simple custom list type *)
Inductive mylist (A : Type) : Type :=
| nil : mylist A
| cons : A -> mylist A -> mylist A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* Deep pattern matching on nested structures with custom types *)
Definition match_pair_list (l : mylist (pair nat nat)) : nat :=
  match l with
  | nil => 0
  | cons (Pair x y) _ => x
  end.

(* Match on first two elements with custom list *)
Definition match_two (l : mylist nat) : nat :=
  match l with
  | nil => 0
  | cons x nil => x
  | cons x (cons y _) => x
  end.

(* Triple nested match with custom lists *)
Definition match_triple (l : mylist (mylist (mylist nat))) : nat :=
  match l with
  | nil => 0
  | cons nil _ => 1
  | cons (cons nil _) _ => 2
  | cons (cons (cons n _) _) _ => n
  end.

(* Pattern match with wildcards at different levels *)
Definition deep_wildcard (p : pair (pair nat nat) (pair nat nat)) : nat :=
  match p with
  | Pair (Pair a _) (Pair _ d) => a
  end.

(* === Test values === *)

(* Tests from original deep_patterns *)
Definition test_deep_some : nat := deep_option (Some (Some (Some 42))).
Definition test_deep_none : nat := deep_option (Some (Some None)).
Definition test_deep_pair : nat := deep_pair ((1, 2), (3, 4)).
Definition test_shape_3 : nat := list_shape [10; 20; 30].
Definition test_shape_long : nat := list_shape [1; 2; 3; 4; 5; 6].
Definition test_deep_sum : nat := deep_sum (OLeft (ILeft 77)).
Definition test_complex : nat := complex_match (Some (5, [10; 20; 30])).
Definition test_guarded : nat := guarded_match (3, 7).

(* Tests from deep_match *)
Definition test_pair_list := match_pair_list (cons (Pair 5 3) nil).
Definition test_two_one := match_two (cons 7 nil).
Definition test_two_many := match_two (cons 7 (cons 8 nil)).
Definition test_triple := match_triple (cons (cons (cons 9 nil) nil) nil).
Definition test_wildcard := deep_wildcard (Pair (Pair 1 2) (Pair 3 4)).

(* Combined test value *)
Definition t : nat :=
  test_deep_some + test_deep_none + test_deep_pair + test_shape_3 +
  test_shape_long + test_deep_sum + test_complex + test_guarded +
  test_pair_list + test_two_one + test_two_many + test_triple + test_wildcard.

End DeepPatterns.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "deep_patterns" DeepPatterns.
