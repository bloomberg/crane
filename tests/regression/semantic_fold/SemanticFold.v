(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Rewrites licensed by declared meanings ([Crane Semantics]): a sum over a
    list carried forward in an accumulator, and small closed definitions
    computed at extraction time.  Each has a counterpart that must be left as
    written. *)
Module SemanticFold.

Inductive list : Type :=
| nil : list
| cons : nat -> list -> list.

Fixpoint seq (start len : nat) : list :=
  match len with
  | O => nil
  | S n => cons start (seq (S start) n)
  end.

(** Whitelisted: unsigned addition of a pure contribution, rewritten to a
    loop.  A list long enough to exhaust the stack frame by frame must sum. *)
Fixpoint sum (l : list) : nat :=
  match l with
  | nil => 0
  | cons x xs => x + sum xs
  end.

Fixpoint sum_scaled (k : nat) (l : list) : nat :=
  match l with
  | nil => 0
  | cons x xs => k * x + 1 + sum_scaled k xs
  end.

(** Declined: [sub] is not associative. *)
Fixpoint alt (l : list) : nat :=
  match l with
  | nil => 0
  | cons x xs => x - alt xs
  end.

(** Declined: [plus'] is the program's own function, with no declared
    meaning. *)
Definition plus' (a b : nat) : nat := a + b.

Fixpoint sum' (l : list) : nat :=
  match l with
  | nil => 0
  | cons x xs => plus' x (sum' xs)
  end.

Inductive color : Type := Red | Green | Blue.

Definition next (c : color) : color :=
  match c with Red => Green | Green => Blue | Blue => Red end.

(** Computed at extraction time. *)
Definition ten_sum : nat := sum (seq 1 10).
Definition scaled : nat := sum_scaled 3 (seq 0 4).
Definition alt_small : nat := alt (seq 1 4).
Definition third : color := next (next Red).

(** Too large for the evaluation budget: left as a computation. *)
Definition big_sum : nat := sum (seq 0 (300 * 100)).

End SemanticFold.

Crane Extraction "semantic_fold" SemanticFold.
