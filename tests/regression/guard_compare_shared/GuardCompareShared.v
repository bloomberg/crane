(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Crane Guard Compare] on a loop-transformed structural comparison over a
    shared variant: the guard answers [Eq] at once where both arguments are
    the same value -- the same block -- and the comparison stops there rather
    than going on through the rest of its body. *)

From Stdlib Require Import PeanoNat.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module GuardCompareShared.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint tcompare (a b : tree) : comparison :=
  match a, b with
  | Leaf, Leaf => Eq
  | Leaf, Node _ _ _ => Lt
  | Node _ _ _, Leaf => Gt
  | Node l1 x1 r1, Node l2 x2 r2 =>
    match tcompare l1 l2 with
    | Eq => match Nat.compare x1 x2 with Eq => tcompare r1 r2 | c => c end
    | c => c
    end
  end.

Fixpoint build (n : nat) : tree :=
  match n with O => Leaf | S m => Node (build m) n Leaf end.

End GuardCompareShared.

Set Crane SharedVariant.
Set Crane Loopify.
Crane Guard Compare GuardCompareShared.tcompare => Eq.
Crane Extraction "guard_compare_shared" GuardCompareShared.
