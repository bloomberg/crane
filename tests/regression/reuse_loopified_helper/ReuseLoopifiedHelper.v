(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane Reuse] under [Set Crane Loopify]: a definition with no
    recursion of its own is left alone by loopification, so its match still
    rebuilds into the block it takes apart when no one else holds it.  The
    recursive [insert] is loopified, and does not take its tree owned for a
    reuse nothing in it would make. *)

From Stdlib Require Import List PeanoNat.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module ReuseLoopifiedHelper.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

(** Rebuilds the root's constructor: a candidate for reuse. *)
Definition bump_root (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k r => Node l (S k) r
  end.

Fixpoint insert (x : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l k r =>
    if x <? k then Node (insert x l) k r
    else if k <? x then Node l k (insert x r)
    else t
  end.

Fixpoint sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l k r => sum l + k + sum r
  end.

End ReuseLoopifiedHelper.

Set Crane SharedVariant.
Set Crane NonAtomicRc.
Set Crane Reuse.
Set Crane Loopify.
Crane Extraction "reuse_loopified_helper" ReuseLoopifiedHelper.
