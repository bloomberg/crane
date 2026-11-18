From Crane Require Import Mapping.NatIntStd Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List NArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Subtraction of a variable from itself: the mapping guard compares the
    variable with itself ([a >= a ? a - a : 0u] for [N.sub a a], [(a - a) > a]
    for [nat]), which -Wtautological-compare rejects under -Werror (the
    comparison forms in self_comparison_werror are fixed).  Values are right. *)
Module SubSelfGuardWerror.

Definition f (a : N) : N := N.sub a a.
Definition g (a : nat) : nat := a - a.
(** [Pos.sub] stops at one, so [p - p] is one. *)
Definition h (p : positive) : positive := Pos.sub p p.

(** The subtraction inside a local fixpoint, of its accumulator. *)
Definition k (l : list nat) (n : N) : N :=
  let fix go (l : list nat) (acc : N) {struct l} : N :=
    match l with [] => N.sub acc acc | _ :: r => go r (N.succ acc) end in
  go l n.

Definition tk : N := k [1; 2] 5.

End SubSelfGuardWerror.

Crane Extraction "sub_self_guard_werror" SubSelfGuardWerror.
