(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Top-level fixpoint with state-threading pair return uses std::move.
   The state param should be non-const and passed via std::move at recursive
   call sites and in std::make_pair return positions. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module FixStateThreading.

(* Reverse a list while counting: state (accumulator) is the first component.
   This is the canonical state-threading pattern: acc is passed through the
   recursion and returned as the first element of the pair. *)
Fixpoint reverse_count (l : list nat) (acc : list nat) : list nat * nat :=
  match l with
  | [] => (acc, 0)
  | x :: rest =>
    let '(acc', n) := reverse_count rest (x :: acc) in
    (acc', n + 1)
  end.

(* Two-state threading: both state params should get move treatment. *)
Fixpoint collect_odds_evens (l : list nat) (odds evens : list nat)
    : list nat * list nat :=
  match l with
  | [] => (odds, evens)
  | x :: rest =>
    if Nat.even x
    then collect_odds_evens rest odds (x :: evens)
    else collect_odds_evens rest (x :: odds) evens
  end.

(* Scalar result: count passes through but the state (acc) gets moved. *)
Fixpoint sum_with_acc (l : list nat) (acc : nat) : nat * nat :=
  match l with
  | [] => (acc, 0)
  | x :: rest =>
    let '(acc', s) := sum_with_acc rest (acc + x) in
    (acc', s + 1)
  end.

(* Test values *)
Definition test_rev : list nat * nat := reverse_count [1; 2; 3] [].
Definition test_ce : list nat * list nat := collect_odds_evens [1; 2; 3; 4; 5] [] [].
Definition test_sum : nat * nat := sum_with_acc [10; 20; 30] 0.

End FixStateThreading.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "fix_state_threading" FixStateThreading.
