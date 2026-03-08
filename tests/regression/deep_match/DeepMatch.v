(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test deep/nested pattern matching *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module DeepMatch.

(* Simple pair type *)
Inductive pair (A B : Type) : Type :=
| Pair : A -> B -> pair A B.

Arguments Pair {A B} _ _.

(* Simple list type *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* Deep pattern matching on nested structures *)
Definition match_pair_list (l : list (pair nat nat)) : nat :=
  match l with
  | nil => 0
  | cons (Pair x y) _ => x
  end.

(* Match on first two elements *)
Definition match_two (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons x nil => x
  | cons x (cons y _) => x
  end.

(* Triple nested match *)
Definition match_triple (l : list (list (list nat))) : nat :=
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

(* Test values *)
Definition test_pair_list := match_pair_list (cons (Pair 5 3) nil).
Definition test_two_one := match_two (cons 7 nil).
Definition test_two_many := match_two (cons 7 (cons 8 nil)).
Definition test_triple := match_triple (cons (cons (cons 9 nil) nil) nil).
Definition test_wildcard := deep_wildcard (Pair (Pair 1 2) (Pair 3 4)).

End DeepMatch.

Crane Extraction "deep_match" DeepMatch.
