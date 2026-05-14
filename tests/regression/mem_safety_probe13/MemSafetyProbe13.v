From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe13.

(** Probe 13: Value-type move semantics and the flatten optimization.

    The flatten optimization (make_owned_param_matches +
    optimize_frame_push_args) marks match branches as owned and
    moves unique_ptr child fields into Enter frames. If a closure
    or continuation simultaneously references the same field,
    the move creates use-after-move.

    Also tests: closures returned from functions that take
    value-type parameters, and deep pattern match nesting
    with closures at each level. *)

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

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

Fixpoint map_list {A B : Type} (f : A -> B) (l : mylist A) : mylist B :=
  match l with
  | mynil => mynil
  | mycons x xs => mycons (f x) (map_list f xs)
  end.

Fixpoint app {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (app xs l2)
  end.

(** TEST 1: Double-recursion on tree where both subtrees
    are used in closures AND in recursive calls.
    Tests if the flatten optimization moves unique_ptr fields
    that are also captured by closures. *)
Fixpoint tree_vals_and_fns (t : tree)
  : mylist nat * mylist (nat -> nat) :=
  match t with
  | Leaf => (mynil, mynil)
  | Node l v r =>
    let '(lvals, lfns) := tree_vals_and_fns l in
    let '(rvals, rfns) := tree_vals_and_fns r in
    let f := fun n => tree_sum l + tree_sum r + n in
    (mycons v (app lvals rvals), mycons f (app lfns rfns))
  end.

Definition test_vals_and_fns : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  let '(vals, fns) := tree_vals_and_fns t in
  let val_sum := sum_list vals in
  let fn_sum := sum_list (map_list (fun f => f 0) fns) in
  val_sum + fn_sum.
(** vals = [7, 3, 11]  val_sum = 21
    fns at root: tree_sum(Node Leaf 3 Leaf) + tree_sum(Node Leaf 11 Leaf) = 3+11 = 14
    fns at left(3): tree_sum Leaf + tree_sum Leaf = 0
    fns at right(11): tree_sum Leaf + tree_sum Leaf = 0
    fn_sum = 14 + 0 + 0 = 14
    Total = 21 + 14 = 35 *)

(** TEST 3: Function that matches twice on same tree.
    First match extracts subtrees, second match on a subtree
    creates a closure capturing the other subtree. *)
Definition double_match (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    match l with
    | Leaf => tree_sum r + v
    | Node ll lv lr =>
      let f := fun n => tree_sum r + tree_sum lr + n in
      f lv + tree_sum ll
    end
  end.

Definition test_double_match : nat :=
  let t := Node
             (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
             10
             (Node Leaf 20 Leaf) in
  double_match t.
(** l = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)
    r = Node Leaf 20 Leaf
    ll = Node Leaf 1 Leaf, lv = 2, lr = Node Leaf 3 Leaf
    f = fun n => tree_sum(Node Leaf 20 Leaf) + tree_sum(Node Leaf 3 Leaf) + n
      = fun n => 20 + 3 + n
    f lv = f 2 = 25
    tree_sum ll = 1
    Total = 25 + 1 = 26 *)

(** TEST 4: Deeply nested tree with closures at EVERY level.
    Each closure captures values from its level AND from the parent.
    Tests stack depth and closure lifetime with deep nesting. *)
Fixpoint make_deep (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (make_deep n') n Leaf
  end.

Fixpoint depth_fns (t : tree) (parent_val : nat)
  : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    let f := fun n => parent_val + v + n in
    mycons f (depth_fns l v)
  end.

Definition test_depth_fns : nat :=
  let t := make_deep 5 in
  let fns := depth_fns t 0 in
  sum_list (map_list (fun f => f 0) fns).
(** make_deep 5 = Node (Node (Node (Node (Node Leaf 1 Leaf) 2 Leaf) 3 Leaf) 4 Leaf) 5 Leaf
    At depth 0: parent_val=0, v=5, f = fun n => 0+5+n = 5
    At depth 1: parent_val=5, v=4, f = fun n => 5+4+n = 9
    At depth 2: parent_val=4, v=3, f = fun n => 4+3+n = 7
    At depth 3: parent_val=3, v=2, f = fun n => 3+2+n = 5
    At depth 4: parent_val=2, v=1, f = fun n => 2+1+n = 3
    Total = 5 + 9 + 7 + 5 + 3 = 29 *)

(** TEST 5: Transform a tree by replacing each value with a
    function, then evaluate. Tests closures in recursive
    tree transformation. *)
Inductive ftree : Type :=
| FLeaf : ftree
| FNode : ftree -> (nat -> nat) -> ftree -> ftree.

Fixpoint tree_to_ftree (t : tree) : ftree :=
  match t with
  | Leaf => FLeaf
  | Node l v r =>
    FNode (tree_to_ftree l) (fun n => v + n) (tree_to_ftree r)
  end.

Fixpoint eval_ftree (ft : ftree) (base : nat) : nat :=
  match ft with
  | FLeaf => 0
  | FNode l f r =>
    eval_ftree l base + f base + eval_ftree r base
  end.

Definition test_ftree : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  let ft := tree_to_ftree t in
  eval_ftree ft 100.
(** f_root = fun n => 7 + n, f_left = fun n => 3 + n, f_right = fun n => 11 + n
    eval with base=100:
    left: 0 + (3+100) + 0 = 103
    root: 103 + (7+100) + right
    right: 0 + (11+100) + 0 = 111
    Total = 103 + 107 + 111 = 321 *)

(** TEST 6: Flatten a tree of lists into a single list,
    where each list element is a closure. *)
Fixpoint flatten_tree_fns (t : tree)
  : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    app (flatten_tree_fns l)
      (mycons (fun n => v + n) (flatten_tree_fns r))
  end.

Definition test_flatten_fns : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  let fns := flatten_tree_fns t in
  sum_list (map_list (fun f => f 1) fns).
(** Inorder: 3, 7, 11.
    Closures: fun n => 3+n, fun n => 7+n, fun n => 11+n
    With base=1: 4 + 8 + 12 = 24 *)

End MemSafetyProbe13.

Crane Extraction "mem_safety_probe13" MemSafetyProbe13.
