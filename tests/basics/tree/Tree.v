(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
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

(* number of nodes (leaf counts as 1) *)
Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + size l + size r
  end.

(* leaf has height 1 *)
Fixpoint height {A} (t : tree A) : nat :=
  match t with
  | leaf => 1
  | node l _ r => 1 + Nat.max (height l) (height r)
  end.

Fixpoint flatten {A : Type} (t : tree A) : list A :=
  match t with
  | leaf => []
  | node l x r => flatten l ++ (x :: flatten r)
  end.

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

Module Tree_Properties.
Import Tree.

Lemma height_pos {A : Type} (t : tree A) : 1 <= height t.
Proof.
  induction t; simpl; lia.
Qed.

Theorem merge_height_max {A : Type}
                         (combine : A -> A -> A)
                         (t1 t2 : tree A) : height (merge combine t1 t2) <= Nat.max (height t1)
                         (height t2).
Proof.
  revert t2.
  induction t1 as [| l1 IHl1 a1 r1 IHr1]; intros t2; destruct t2 as [| l2 a2 r2]; simpl.
  - (* leaf, leaf *)
    lia.
  - (* leaf, node *)
    pose proof (height_pos l2). pose proof (height_pos r2). lia.
  - (* node, leaf *)
    pose proof (height_pos l1). pose proof (height_pos r1). lia.
  - (* node, node *)
    specialize (IHl1 l2).
    specialize (IHr1 r2).
    lia.
Qed.

End Tree_Properties.

From Crane Require Extraction.
Crane Extraction TestCompile "tree" Tree.
