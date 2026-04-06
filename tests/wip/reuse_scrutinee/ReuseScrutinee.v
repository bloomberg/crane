From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ReuseScrutinee.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** Extract the value from the left subtree.
    This accesses the Node's d_a0 field (left subtree). *)
Definition left_val (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ _ =>
    match l with
    | Leaf => 0
    | Node _ v _ => v
    end
  end.

(** Extract the value from the right subtree. *)
Definition right_val (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ _ r =>
    match r with
    | Leaf => 0
    | Node _ v _ => v
    end
  end.

(** Sum of left and right subtree values. *)
Definition subtree_sum (t : tree) : nat :=
  left_val t + right_val t.

(** REUSE BUG TRIGGER:
    The match on t returns Node Leaf (subtree_sum t) Leaf.
    If the reuse optimization fires (t.use_count() == 1):
    1. Fields are moved out: l = move(d_a0), r = move(d_a2)
       → d_a0 and d_a2 are now null
    2. New values are computed: subtree_sum(t) accesses t's subtrees
       → t's d_a0 is null → left_val dereferences null → CRASH *)
Definition reuse_bug : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  match t with
  | Leaf => 0
  | Node l v r =>
    match Node Leaf (subtree_sum t) Leaf with
    | Leaf => 0
    | Node _ result _ => result
    end
  end.

(** Direct version: the result directly uses the scrutinee in a
    tail constructor that could trigger reuse. *)
Definition reuse_direct : tree :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  match t with
  | Leaf => Leaf
  | Node l v r => Node Leaf (subtree_sum t) r
  end.

(** Expected: subtree_sum on Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
    = left_val + right_val = 10 + 30 = 40 *)
Definition expected_sum : nat :=
  subtree_sum (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).

End ReuseScrutinee.

Crane Extraction "reuse_scrutinee" ReuseScrutinee.
