(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test nested inductive types (inductives that use other inductives) *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module NestedInductive.

(* Simple list for nesting *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* Rose tree - tree with list of children (nested inductive) *)
Inductive rose (A : Type) : Type :=
| Node : A -> list (rose A) -> rose A.

Arguments Node {A} _ _.

(* Get the root value *)
Definition root {A : Type} (t : rose A) : A :=
  match t with
  | Node x _ => x
  end.

(* Get list length *)
Fixpoint list_length {A : Type} (l : list A) : nat :=
  match l with
  | nil => zero
  | cons _ rest => Nat.add one (list_length rest)
  end.

(* Get children count (not recursive into children) *)
Definition children_count {A : Type} (t : rose A) : nat :=
  match t with
  | Node _ children => list_length children
  end.

(* Test rose tree *)
Definition leaf (n : nat) : rose nat := Node n nil.
Definition small_tree : rose nat :=
  Node one (cons (leaf two) (cons (leaf three) nil)).

Definition bigger_tree : rose nat :=
  Node one (cons small_tree (cons (leaf four) nil)).

(* Test values *)
Definition test_root_leaf := root (leaf five).
Definition test_root_small := root small_tree.
Definition test_children_leaf := children_count (leaf five).
Definition test_children_small := children_count small_tree.
Definition test_children_bigger := children_count bigger_tree.

End NestedInductive.

Crane Extraction "nested_inductive" NestedInductive.
