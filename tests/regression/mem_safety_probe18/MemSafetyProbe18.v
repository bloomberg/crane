From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe18.

(** Probe 18: Complex ownership handoff patterns.

    Attack vectors:
    1. Functions where the SAME argument appears in multiple positions
       of a single constructor call (potential double-move)
    2. let-binding a function of a value, then using the value AGAIN
       (ownership tracking across let-bindings)
    3. Passing a closure to a higher-order function that calls it
       multiple times (std::function copy semantics)
    4. Complex constructor nesting where tree values appear at
       multiple levels *)

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

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

Fixpoint myapp {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (myapp xs l2)
  end.

Fixpoint map_list {A B : Type} (f : A -> B) (l : mylist A) : mylist B :=
  match l with
  | mynil => mynil
  | mycons x xs => mycons (f x) (map_list f xs)
  end.

(** TEST 1: Same tree used in TWO different positions of a single
    constructor. Tests whether the tree is properly cloned. *)
Definition dup_tree (t : tree) : tree :=
  Node t 0 t.

Definition test_dup : nat :=
  let t := Node Leaf 42 Leaf in
  tree_sum (dup_tree t).
(** Node(Node(Leaf,42,Leaf), 0, Node(Leaf,42,Leaf)) = 42 + 0 + 42 = 84 *)

(** TEST 2: Let-bind tree_sum, then use the tree again.
    The tree should NOT be consumed by tree_sum. *)
Definition let_reuse (t : tree) : nat :=
  let s := tree_sum t in
  s + tree_sum t.

Definition test_let_reuse : nat :=
  let_reuse (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)).
(** tree_sum = 30. 30 + 30 = 60 *)

(** TEST 3: Apply a higher-order function multiple times
    to a closure that captures a tree. *)
Definition apply_twice (f : nat -> nat) (x : nat) : nat :=
  f (f x).

Definition test_apply_twice : nat :=
  let t := Node Leaf 7 Leaf in
  let f := fun n => tree_sum t + n in
  apply_twice f 0.
(** f(0) = 7, f(7) = 14. Result = 14 *)

(** TEST 4: Build a tree from a tree, using it at multiple levels. *)
Definition tree_from_tree (t : tree) : tree :=
  Node (Node t 0 Leaf) (tree_sum t) (Node Leaf 0 t).

Definition test_tree_from_tree : nat :=
  let t := Node Leaf 5 Leaf in
  tree_sum (tree_from_tree t).
(** tree_from_tree t = Node(Node(t,0,Leaf), 5, Node(Leaf,0,t))
    = Node(Node(Node(Leaf,5,Leaf),0,Leaf), 5, Node(Leaf,0,Node(Leaf,5,Leaf)))
    sum = (5+0+0) + 5 + (0+0+5) = 5 + 5 + 5 = 15 *)

(** TEST 5: Complex fold that builds a tree from a list. *)
Fixpoint fold_left_tree (l : mylist nat) (acc : tree) : tree :=
  match l with
  | mynil => acc
  | mycons x xs => fold_left_tree xs (Node acc x Leaf)
  end.

Definition test_fold_tree : nat :=
  let l := mycons 1 (mycons 2 (mycons 3 mynil)) in
  tree_sum (fold_left_tree l Leaf).
(** fold: Leaf -> Node(Leaf,1,Leaf) -> Node(Node(Leaf,1,Leaf),2,Leaf)
    -> Node(Node(Node(Leaf,1,Leaf),2,Leaf),3,Leaf)
    sum = 1 + 2 + 3 = 6 *)

(** TEST 6: Concat two lists, using both in the result. *)
Fixpoint concat_flat {A : Type} (ls : mylist (mylist A)) : mylist A :=
  match ls with
  | mynil => mynil
  | mycons l rest => myapp l (concat_flat rest)
  end.

Definition test_concat : nat :=
  let l1 := mycons 1 (mycons 2 mynil) in
  let l2 := mycons 3 (mycons 4 mynil) in
  let l3 := mycons 5 (mycons 6 mynil) in
  let ls := mycons l1 (mycons l2 (mycons l3 mynil)) in
  sum_list (concat_flat ls).
(** [1,2,3,4,5,6]. Sum = 21 *)

(** TEST 7: Use a value type in a chain of let-bindings where
    each binding transforms the tree. *)
Definition chain_transforms (t : tree) : nat :=
  let t1 := Node t 0 Leaf in
  let t2 := Node Leaf 0 t1 in
  let t3 := Node t2 0 t in
  tree_sum t3.

Definition test_chain : nat :=
  let t := Node Leaf 10 Leaf in
  chain_transforms t.
(** t1 = Node(t, 0, Leaf) sum=10
    t2 = Node(Leaf, 0, t1) sum=10
    t3 = Node(t2, 0, t) sum=10+0+10 = 20
    Total = 20 *)

(** TEST 8: Nested constructor building: build a list of trees
    using the same tree in different positions. *)
Fixpoint build_tree_list (t : tree) (n : nat) : mylist tree :=
  match n with
  | O => mynil
  | S n' => mycons (Node t n Leaf) (build_tree_list t n')
  end.

Fixpoint sum_tree_list (l : mylist tree) : nat :=
  match l with
  | mynil => 0
  | mycons t rest => tree_sum t + sum_tree_list rest
  end.

Definition test_build_tree_list : nat :=
  let t := Node Leaf 10 Leaf in
  let trees := build_tree_list t 3 in
  sum_tree_list trees.
(** tree at n=3: Node(t, 3, Leaf) = 10+3 = 13
    tree at n=2: Node(t, 2, Leaf) = 10+2 = 12
    tree at n=1: Node(t, 1, Leaf) = 10+1 = 11
    Total = 13+12+11 = 36 *)

(** TEST 9: Triple-use of a tree: compute sum, build a new tree, compute sum again *)
Definition triple_use (t : tree) : nat :=
  let s1 := tree_sum t in
  let t2 := Node t s1 t in
  let s2 := tree_sum t2 in
  s1 + s2.

Definition test_triple_use : nat :=
  triple_use (Node Leaf 7 Leaf).
(** s1 = 7. t2 = Node(t, 7, t). s2 = 7+7+7 = 21. Result = 7+21 = 28 *)

End MemSafetyProbe18.

Crane Extraction "mem_safety_probe18" MemSafetyProbe18.
