(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane Reuse] over [Set Crane SharedVariant]: a match on a value no
    one else holds rebuilds its constructor in the matched block.  A search
    tree updated along a path, and a list mapped, keep their blocks when
    unique; a tree still held elsewhere is copied, and the other holder sees
    it unchanged. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedVariantReuse.

Inductive tree := Leaf | Node : tree -> nat -> nat -> tree -> tree.

Fixpoint insert (k v : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf k v Leaf
  | Node l k' v' r =>
      if Nat.ltb k k' then Node (insert k v l) k' v' r
      else if Nat.ltb k' k then Node l k' v' (insert k v r)
      else Node l k v r
  end.

Fixpoint find (k : nat) (t : tree) : option nat :=
  match t with
  | Leaf => None
  | Node l k' v r =>
      if Nat.ltb k k' then find k l else if Nat.ltb k' k then find k r else Some v
  end.

Inductive lst := Nil | Cons : nat -> lst -> lst.

Fixpoint bump (l : lst) : lst :=
  match l with Nil => Nil | Cons x xs => Cons (S x) (bump xs) end.

Fixpoint total (l : lst) : nat :=
  match l with Nil => 0 | Cons x xs => x + total xs end.

End SharedVariantReuse.

Set Crane SharedVariant.
Set Crane Reuse.
Crane Extraction "shared_variant_reuse" SharedVariantReuse.
