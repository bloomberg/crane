(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Module Tree.

(** A polymorphic binary tree. A [tree] is either a [leaf] or a
    [node] with a left subtree, a value, and a right subtree. *)
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} t1 x t2.

(** Returns [true] if [t] is a [leaf], [false] otherwise. *)
Definition is_leaf {A} (t : tree A) : bool :=
  match t with
  | leaf => true
  | node _ _ _ => false
  end.

(** Number of nodes in tree [t]. A [leaf] counts as 1. *)
Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + size l + size r
  end.

(** Height of tree [t]. A [leaf] has height 1. *)
Fixpoint height {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + Nat.max (height l) (height r)
  end.

(** Collect all values in [t] into a list via in-order traversal. *)
Fixpoint flatten {A : Type} (t : tree A) : list A :=
  match t with
  | leaf => []
  | node l x r => flatten l ++ (x :: flatten r)
  end.

(** Merge two trees [t1] and [t2] element-wise using [combine].
    Subtrees beyond the shape of the other tree are truncated. *)
Fixpoint merge {A : Type}
               (combine : A -> A -> A)
               (t1 t2 : tree A) : tree A :=
  match t1 with
  | leaf =>
      match t2 with
      | leaf => leaf
      | node l a r => node leaf a leaf
      end
  | node l1 a1 r1 =>
      match t2 with
      | leaf => node leaf a1 leaf
      | node l2 a2 r2 =>
          node (merge combine l1 l2)
               (combine a1 a2)
               (merge combine r1 r2)
      end
  end.

Definition tree1 := node (node leaf 3 (node leaf 7 leaf)) 1 (node leaf 4 (node (node leaf 6 leaf) 2 leaf)).

End Tree.

Require Crane.Extraction.
Crane Extraction "tree" Tree.
