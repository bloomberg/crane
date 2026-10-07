(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane SharedVariant]: a recursive inductive's value is one word,
    its alternative with fields in a counted block, and a recursive field
    holds the value itself.  A search tree is built, rebuilt along a path
    sharing the subtrees it does not touch, and read back; a list is mapped
    and summed; and a long list, built and measured by loops, is dropped, which must free its blocks
    without recursing. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedVariantBasic.

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

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ _ r => 1 + size l + size r end.

Definition t0 : tree := fold_left (fun t k => insert k (k * 10) t) [5; 3; 8; 1; 4; 7; 9] Leaf.
(* [t1] shares every subtree of [t0] off the path to 4. *)
Definition t1 : tree := insert 4 44 t0.

Definition tree_result : nat :=
  match find 4 t0, find 4 t1, find 9 t1 with
  | Some a, Some b, Some c => a + b + c + size t0 + size t1
  | _, _, _ => 0
  end.

Definition bump (l : list nat) : list nat := map S l.

Definition list_result : nat := fold_left Nat.add (bump [1; 2; 3]) 0.

Definition long_result (n : nat) : nat := length (seq 0 n).

End SharedVariantBasic.

Set Crane SharedVariant.
Crane Loopify seq length.
Crane Extraction "shared_variant_basic" SharedVariantBasic.
