From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe9.

(** These tests probe patterns where closures accumulate
    during tree traversal. Each closure captures subtrees
    (unique_ptr fields) that are also used in recursive calls.
    The captures must be independent clones. *)

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

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => 1 + length xs
  end.

Fixpoint sum_fns (l : mylist (nat -> nat)) : nat :=
  match l with
  | mynil => 0
  | mycons f rest => f 0 + sum_fns rest
  end.

(** TEST 1: Collect closures that each capture a subtree.
    Both l and r are captured AND used in recursive calls. *)
Fixpoint collect_subtree_sums (t : tree)
  (acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match t with
  | Leaf => acc
  | Node l v r =>
    let f := fun _n => tree_sum l + v + tree_sum r in
    collect_subtree_sums l
      (collect_subtree_sums r (mycons f acc))
  end.

Definition test_collect : nat :=
  let t := Node (Node Leaf 5 Leaf) 10
               (Node Leaf 15 (Node Leaf 20 Leaf)) in
  let fns := collect_subtree_sums t mynil in
  sum_fns fns.
(** Tree:
       10
      /  \
     5    15
           \
           20

    Traversal (collect_subtree_sums):
    At root(10): f = fun _n => tree_sum(Node Leaf 5 Leaf)
                              + 10
                              + tree_sum(Node Leaf 15 (Node Leaf 20 Leaf))
                 = 5 + 10 + (15 + 20) = 50
    At 15: f = fun _n => tree_sum(Leaf) + 15 + tree_sum(Node Leaf 20 Leaf)
             = 0 + 15 + 20 = 35
    At 20: f = fun _n => tree_sum(Leaf) + 20 + tree_sum(Leaf)
             = 0 + 20 + 0 = 20
    At 5: f = fun _n => tree_sum(Leaf) + 5 + tree_sum(Leaf)
            = 0 + 5 + 0 = 5

    fns = [f5, f20, f15, f10] (reversed order of traversal)
    sum_fns = 5 + 20 + 35 + 50 = 110 *)

(** TEST 2: Similar but each closure captures ONLY the left subtree.
    The left subtree is shared between closure and recursive call. *)
Fixpoint collect_left_sums (t : tree)
  (acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match t with
  | Leaf => acc
  | Node l v r =>
    let f := fun _n => tree_sum l in
    collect_left_sums l (collect_left_sums r (mycons f acc))
  end.

Definition test_left_sums : nat :=
  let t := Node (Node (Node Leaf 3 Leaf) 7 Leaf) 10
               (Node Leaf 15 Leaf) in
  let fns := collect_left_sums t mynil in
  sum_fns fns.
(** Tree:
         10
        /  \
       7    15
      /
     3

    At root(10): f = tree_sum(Node(Node Leaf 3 Leaf) 7 Leaf) = 3+7 = 10
    At 7: f = tree_sum(Node Leaf 3 Leaf) = 3
    At 3: f = tree_sum(Leaf) = 0
    At 15: f = tree_sum(Leaf) = 0

    sum = 0 + 0 + 3 + 10 = 13 *)

(** TEST 3: Build closures from list where each closure
    captures the tail and a computed value. *)
Fixpoint list_accum_closures (l : mylist nat)
  (acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match l with
  | mynil => acc
  | mycons x xs =>
    let tail_len := length xs in
    let f := fun _n => x * tail_len in
    list_accum_closures xs (mycons f acc)
  end.

Definition test_list_accum : nat :=
  let l := mycons 10 (mycons 20 (mycons 30 mynil)) in
  let fns := list_accum_closures l mynil in
  sum_fns fns.
(** x=10, tail_len=2: f = 20
    x=20, tail_len=1: f = 20
    x=30, tail_len=0: f = 0
    fns = [f30, f20, f10] reversed
    sum = 0 + 20 + 20 = 40 *)

(** TEST 4: Closures that capture a tree AND its subtrees
    independently — tests that cloning produces independent
    copies. Modify one subtree's computation after capture. *)
Definition triple_capture (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    let f1 := fun _n => tree_sum l in
    let f2 := fun _n => tree_sum r in
    let f3 := fun _n => tree_sum t in
    f1 0 + f2 0 + f3 0
  end.

Definition test_triple : nat :=
  triple_capture (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** f1 = tree_sum(Node Leaf 10 Leaf) = 10
    f2 = tree_sum(Node Leaf 30 Leaf) = 30
    f3 = tree_sum(Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) = 60
    Total = 100 *)

(** TEST 5: Mutual use pattern — the left subtree is used to compute
    a value that's passed to a closure that captures the right subtree. *)
Definition cross_capture (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    let lsum := tree_sum l in
    let f := fun n => tree_sum r + n in
    f lsum + f v
  end.

Definition test_cross : nat :=
  cross_capture (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)).
(** lsum = tree_sum(Node Leaf 5 Leaf) = 5
    f n = tree_sum(Node Leaf 15 Leaf) + n = 15 + n
    f lsum = 15 + 5 = 20
    f v = 15 + 10 = 25
    Total = 45 *)

(** TEST 6: Stress test — large tree, many closures. *)
Fixpoint make_balanced (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (make_balanced n') n (make_balanced n')
  end.

Definition test_stress : nat :=
  let t := make_balanced 5 in
  let fns := collect_left_sums t mynil in
  sum_fns fns.
(** make_balanced 5: tree with 2^5-1 = 31 nodes.
    Each internal node creates a closure that computes tree_sum of its left child.
    This tests 31 closures, each capturing a different subtree. *)

End MemSafetyProbe9.

Crane Extraction "mem_safety_probe9" MemSafetyProbe9.
