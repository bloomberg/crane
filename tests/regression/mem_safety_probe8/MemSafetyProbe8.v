From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe8.

(** These tests probe the interaction between:
    1. OWNED tree parameters in loopified functions
    2. Double recursion (f l + v + f r) creating _After frames
    3. The flatten optimization (optimize_frame_push_args) that adds
       std::move to _Enter frame pushes

    If an _After frame stores a raw pointer (d_a0.get()) to a child
    of an owned tree, and the tree is destroyed at the end of the
    _Enter handler, the raw pointer would dangle. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** TEST 1: Non-method tree traversal with double recursion.
    dummy ensures tree is NOT the first arg (avoiding methodification).
    tree is the second arg — should be owned if it doesn't escape. *)
Fixpoint tree_sum_ext (dummy : nat) (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum_ext 0 l + v + tree_sum_ext 0 r
  end.

Definition test_tree_sum : nat :=
  tree_sum_ext 0 (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** 10 + 20 + 30 = 60 *)

(** TEST 2: Same but with a more complex computation to prevent
    the optimizer from simplifying. *)
Fixpoint tree_weighted (dummy : nat) (t : tree) (depth : nat) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    tree_weighted 0 l (1 + depth) + v * depth + tree_weighted 0 r (1 + depth)
  end.

Definition test_tree_weighted : nat :=
  tree_weighted 0 (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) 1.
(** tree_weighted _ (Node Leaf 10 Leaf) 2 = 0 + 10*2 + 0 = 20
    tree_weighted _ (Node Leaf 30 Leaf) 2 = 0 + 30*2 + 0 = 60
    root: 20 + 20*1 + 60 = 100 *)

(** TEST 3: Deep tree traversal — more iterations, more frames. *)
Fixpoint make_left_spine (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (make_left_spine n') n Leaf
  end.

Definition test_deep_tree : nat :=
  tree_sum_ext 0 (make_left_spine 100).
(** Sum of 1+2+...+100 = 5050 *)

(** TEST 4: Tree traversal where both recursive calls use
    different subtrees — _After frame must hold one while
    processing the other. *)
Fixpoint tree_collect (dummy : nat) (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    let left := tree_collect 0 l in
    let right := tree_collect 0 r in
    left + v + right
  end.

Definition test_collect : nat :=
  tree_collect 0 (Node (Node (Node Leaf 5 Leaf) 10 Leaf) 20
                       (Node Leaf 30 (Node Leaf 40 Leaf))).
(** 5 + 10 + 20 + 30 + 40 = 105 *)

(** TEST 5: Tree function where the tree is consumed (not
    used after recursive calls) — maximally owned. *)
Fixpoint tree_flatten (dummy : nat) (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r =>
    tree_flatten 0 l * v * tree_flatten 0 r
  end.

Definition test_flatten : nat :=
  tree_flatten 0 (Node (Node Leaf 2 Leaf) 3 (Node Leaf 5 Leaf)).
(** tree_flatten (Node Leaf 2 Leaf) = 1 * 2 * 1 = 2
    tree_flatten (Node Leaf 5 Leaf) = 1 * 5 * 1 = 5
    root: 2 * 3 * 5 = 30 *)

(** TEST 6: Pass tree as a higher-order function argument
    to prevent methodification completely. *)
Definition tree_size_via_fold (t : tree) : nat :=
  let fix go (dummy : nat) (t : tree) : nat :=
    match t with
    | Leaf => 0
    | Node l v r => 1 + go 0 l + go 0 r
    end
  in go 0 t.

Definition test_fold_size : nat :=
  tree_size_via_fold (Node (Node Leaf 1 Leaf) 2
                           (Node (Node Leaf 3 Leaf) 4 Leaf)).
(** 4 nodes *)

End MemSafetyProbe8.

Crane Extraction "mem_safety_probe8" MemSafetyProbe8.
