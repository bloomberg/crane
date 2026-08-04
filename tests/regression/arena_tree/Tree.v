(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: exercises Crane Arena (opt-in arena extraction) on a recursive tree. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Module Tree.

Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} t1 x t2.

Definition is_leaf {A} (t : tree A) : bool :=
  match t with
  | leaf => true
  | node _ _ _ => false
  end.

Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + size l + size r
  end.

Fixpoint mirror {A} (t : tree A) : tree A :=
  match t with
  | leaf => leaf
  | node l x r => node (mirror r) x (mirror l)
  end.

End Tree.

Require Crane.Extraction.
Crane Arena Tree.tree.
Crane Extraction "arena_tree" Tree.
