(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Regression test for switch-case break in loopified code.
    A recursive function matching on a 3+ constructor enum generates a
    switch statement.  Loopification replaces returns with _result
    assignments and stack pushes — without break after each case, the
    generated C++ falls through and produces wrong results or crashes. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifySwitchBreak.

Inductive tag : Type :=
| Add : tag
| Mul : tag
| Keep : tag.

(** [eval_ops ops acc] folds a list of (tag, value) pairs into an accumulator.
    Each tag selects a different operation:
      Add  -> acc + value
      Mul  -> acc * value
      Keep -> acc  (ignore value)
    The function is structurally recursive on the list, and pattern-matches
    on the tag inside the Cons branch.  Crane extracts the tag match as a
    switch statement; loopification must emit break after each case. *)
Fixpoint eval_ops (ops : list (tag * nat)) (acc : nat) : nat :=
  match ops with
  | nil => acc
  | cons (t, v) rest =>
    match t with
    | Add  => eval_ops rest (Nat.add acc v)
    | Mul  => eval_ops rest (Nat.mul acc v)
    | Keep => eval_ops rest acc
    end
  end.

(** A variant that builds a result list, so the recursive calls are
    non-tail — this forces loopification to use continuation frames
    (not just tail-call optimisation), exercising the break path in
    non-tail switch branches. *)
Fixpoint collect_ops (ops : list (tag * nat)) (acc : nat) : list nat :=
  match ops with
  | nil => cons acc nil
  | cons (t, v) rest =>
    match t with
    | Add  => cons acc (collect_ops rest (Nat.add acc v))
    | Mul  => cons acc (collect_ops rest (Nat.mul acc v))
    | Keep => cons acc (collect_ops rest acc)
    end
  end.

(** [count_tags tag ops] counts how many times a given tag appears.
    All three branches of the switch recurse; without break, EQ would
    fall through to the next case and produce an incorrect count. *)
Fixpoint count_tag (t : tag) (ops : list (tag * nat)) : nat :=
  match ops with
  | nil => 0
  | cons (t', _) rest =>
    match t, t' with
    | Add,  Add  => S (count_tag t rest)
    | Mul,  Mul  => S (count_tag t rest)
    | Keep, Keep => S (count_tag t rest)
    | _,    _    => count_tag t rest
    end
  end.

End LoopifySwitchBreak.

Set Crane Loopify.
Crane Extraction "loopify_switch_break" LoopifySwitchBreak.
