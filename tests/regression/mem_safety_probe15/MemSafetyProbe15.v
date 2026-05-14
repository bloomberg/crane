From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe15.

(** Probe 15: Focused on finding RUNTIME memory safety bugs.

    Key attack vectors:
    1. Flatten optimization: v_mut() + unique_ptr field moves
       in loopified Enter frames
    2. Value-type tree where subtrees are read AFTER being
       potentially moved by the frame push
    3. Closures that capture match bindings from owned matches
    4. Deep trees with many unique_ptr indirections *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint myapp {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (myapp xs l2)
  end.

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => 1 + length xs
  end.

(** TEST 1: Tree flattening where left subtree is used AFTER
    right subtree recursive call.
    In loopified code, the Enter frame for the right subtree
    may move the left subtree's pointer. *)
Fixpoint flatten (t : tree) : mylist nat :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    myapp (flatten l) (mycons v (flatten r))
  end.

Definition test_flatten : nat :=
  let t := Node
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
    4
    (Node (Node Leaf 5 Leaf) 6 (Node Leaf 7 Leaf)) in
  sum_list (flatten t).
(** Inorder: 1,2,3,4,5,6,7. Sum = 28 *)

(** TEST 2: Tree to list where each element is the sum of
    its subtree. Uses both subtrees for computation AND recursion. *)
Fixpoint subtree_sums (t : tree) : mylist nat :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (tree_sum l + v + tree_sum r)
      (myapp (subtree_sums l) (subtree_sums r))
  end.

Definition test_subtree_sums : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  sum_list (subtree_sums t).
(** Root subtree sum: 3 + 7 + 11 = 21
    Left(3): 0 + 3 + 0 = 3
    Right(11): 0 + 11 + 0 = 11
    Total = 21 + 3 + 11 = 35 *)

(** TEST 3: Tree mirror that uses both subtrees. *)
Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (mirror r) v (mirror l)
  end.

Definition test_mirror : nat :=
  let t := Node (Node Leaf 1 (Node Leaf 2 Leaf)) 3 (Node Leaf 4 Leaf) in
  tree_sum (mirror t).
(** mirror preserves tree_sum. Sum = 1+2+3+4 = 10 *)

(** TEST 4: Tree zipping — combine two trees into one. *)
Fixpoint zip_trees (t1 t2 : tree) : tree :=
  match t1 with
  | Leaf => t2
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => t1
    | Node l2 v2 r2 =>
      Node (zip_trees l1 l2) (v1 + v2) (zip_trees r1 r2)
    end
  end.

Definition test_zip : nat :=
  let t1 := Node (Node Leaf 1 Leaf) 10 (Node Leaf 2 Leaf) in
  let t2 := Node (Node Leaf 3 Leaf) 20 (Node Leaf 4 Leaf) in
  tree_sum (zip_trees t1 t2).
(** (1+3) + (10+20) + (2+4) = 4 + 30 + 6 = 40 *)

(** TEST 5: Deep left-spine tree.
    Stresses the frame stack depth. *)
Fixpoint left_spine (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (left_spine n') n Leaf
  end.

Definition test_deep_spine : nat :=
  tree_sum (left_spine 100).
(** Sum = 100+99+...+1 = 5050 *)

(** TEST 6: List reversal using accumulator.
    Tests owned parameter match optimization. *)
Fixpoint rev_aux {A : Type} (l acc : mylist A) : mylist A :=
  match l with
  | mynil => acc
  | mycons x xs => rev_aux xs (mycons x acc)
  end.

Definition test_rev : nat :=
  let l := mycons 1 (mycons 2 (mycons 3 (mycons 4 mynil))) in
  let r := rev_aux l mynil in
  sum_list r.
(** Sum = 1+2+3+4 = 10 *)

(** TEST 7: Two passes over the same tree.
    First pass collects values, second pass computes sums.
    Tests that the tree is not consumed by the first pass. *)
Definition two_pass (t : tree) : nat :=
  let vals := flatten t in
  let sums := subtree_sums t in
  sum_list vals + sum_list sums.

Definition test_two_pass : nat :=
  two_pass (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)).
(** flatten: [3,7,11] sum=21
    subtree_sums: [21,3,11] sum=35
    Total = 21 + 35 = 56 *)

(** TEST 8: Map over a list, transforming each element. *)
Fixpoint map_list {A B : Type} (f : A -> B) (l : mylist A) : mylist B :=
  match l with
  | mynil => mynil
  | mycons x xs => mycons (f x) (map_list f xs)
  end.

Definition test_map : nat :=
  let l := mycons 10 (mycons 20 (mycons 30 mynil)) in
  let l2 := map_list (fun x => x + 1) l in
  sum_list l2.
(** [11, 21, 31] sum = 63 *)

(** TEST 9: Build a large tree and verify all values are preserved. *)
Fixpoint make_tree (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (make_tree n') n (make_tree n')
  end.

Definition test_large_tree : nat :=
  tree_sum (make_tree 6).
(** make_tree 6: complete binary tree.
    Sum at level k = k * 2^(k-1) for k=1..6
    = 1*1 + 2*2 + 3*4 + 4*8 + 5*16 + 6*32
    = 1 + 4 + 12 + 32 + 80 + 192 = 321
    Wait, more precisely:
    make_tree 0 = Leaf (sum=0)
    make_tree 1 = Node Leaf 1 Leaf (sum=1)
    make_tree 2 = Node (make_tree 1) 2 (make_tree 1) = 1+2+1 = 4
    make_tree 3 = 4+3+4 = 11
    make_tree 4 = 11+4+11 = 26
    make_tree 5 = 26+5+26 = 57
    make_tree 6 = 57+6+57 = 120 *)

End MemSafetyProbe15.

Crane Extraction "mem_safety_probe15" MemSafetyProbe15.
