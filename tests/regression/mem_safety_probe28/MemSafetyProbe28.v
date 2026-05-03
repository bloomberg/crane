From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Require Import List.
Import ListNotations.

Set Crane Loopify.

Module MemSafetyProbe28.

(** Probe 28: Move optimization in loopified code.

    Attack vector: The flatten optimization (make_owned_param_matches +
    optimize_frame_push_args) moves *(d_child) into _Enter frames when
    the parameter is non-pointer-safe. A function with TWO tree params
    where t1 is the structural argument and t2 varies non-structurally
    makes t2 NOT pointer-safe. If t2's children are moved via the
    optimization but t2 is also used non-recursively (e.g. tree_sum t2),
    the _After frame references corrupted data.

    Key insight: Coq's structural recursion guarantees that single-tree
    recursion always passes CPPderef sub-terms, making the param
    pointer-safe. Two-param functions break this when the non-structural
    param varies non-uniformly. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Fixpoint tree_depth (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 1 + max (tree_depth l) (tree_depth r)
  end.

(** TEST 1: zip_trees - Two tree params, t1 structural, t2 non-structural.
    t2 is NOT pointer-safe because some calls pass Leaf (not CPPderef).
    In the Node/Node branch, t2's children are used for recursion AND
    tree_sum t2 uses the whole tree. If the optimization moves *(l2),
    tree_sum t2 might see corrupted data. *)
Fixpoint zip_trees (t1 t2 : tree) : nat :=
  match t1 with
  | Leaf => tree_sum t2
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => v1 + zip_trees l1 Leaf + zip_trees r1 Leaf
    | Node l2 v2 r2 =>
      zip_trees l1 l2 + v1 + v2 + zip_trees r1 r2 + tree_sum t2
    end
  end.

Definition test_zip_trees : nat :=
  zip_trees
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
    (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** t1 = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf), sum1 = 6
    t2 = Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf), sum2 = 60

    zip_trees t1 t2:
    Match t1=Node, t2=Node:
      zip_trees (NL1L) (NL10L) + 2 + 20 + zip_trees (NL3L) (NL30L) + 60

    zip_trees (NL1L) (NL10L):
      Match Node/Node:
      zip_trees Leaf Leaf + 1 + 10 + zip_trees Leaf Leaf + tree_sum (NL10L)
      = 0 + 1 + 10 + 0 + 10 = 21

    zip_trees (NL3L) (NL30L):
      Match Node/Node:
      zip_trees Leaf Leaf + 3 + 30 + zip_trees Leaf Leaf + tree_sum (NL30L)
      = 0 + 3 + 30 + 0 + 30 = 63

    Total: 21 + 2 + 20 + 63 + 60 = 166 *)

(** TEST 2: zip_depth - Similar but uses tree_depth on t2.
    Tests a different tree traversal on the non-pointer-safe param. *)
Fixpoint zip_depth (t1 t2 : tree) : nat :=
  match t1 with
  | Leaf => tree_depth t2
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => v1 + zip_depth l1 Leaf + zip_depth r1 Leaf
    | Node l2 v2 r2 =>
      zip_depth l1 l2 + tree_depth t2 + zip_depth r1 r2
    end
  end.

Definition test_zip_depth : nat :=
  zip_depth
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
    (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** t2 depth = 2
    zip_depth (NL1L) (NL10L): Node/Node
      zip_depth L L + depth(NL10L) + zip_depth L L
      = 0 + 1 + 0 = 1
    zip_depth (NL3L) (NL30L): Node/Node
      zip_depth L L + depth(NL30L) + zip_depth L L
      = 0 + 1 + 0 = 1
    zip_depth t1 t2: 1 + 2 + 1 = 4 *)

(** TEST 3: zip_and_build - Recurse and also construct using t2's children.
    t2's left child is used for recursion AND returned as part of result. *)
Fixpoint zip_and_sum (t1 t2 : tree) : nat :=
  match t1 with
  | Leaf => tree_sum t2
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => zip_and_sum l1 Leaf + v1 + zip_and_sum r1 Leaf
    | Node l2 v2 r2 =>
      zip_and_sum l1 l2 + v2 + zip_and_sum r1 r2 + tree_sum l2 + tree_sum r2
    end
  end.

Definition test_zip_and_sum : nat :=
  zip_and_sum
    (Node Leaf 5 Leaf)
    (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** t1 = Node Leaf 5 Leaf
    t2 = Node (NL10L) 20 (NL30L)
    Match Node/Node:
      zip_and_sum Leaf (NL10L) + 20 + zip_and_sum Leaf (NL30L) + tree_sum(NL10L) + tree_sum(NL30L)
      = 10 + 20 + 30 + 10 + 30 = 100 *)

(** TEST 4: double_zip - Both t1 and t2 are trees, but t2 is used
    in a different way for each call. Makes t2 non-pointer-safe. *)
Fixpoint double_zip (t1 t2 : tree) : nat :=
  match t1 with
  | Leaf => tree_sum t2
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => double_zip l1 t2 + v1 + double_zip r1 t2
    | Node l2 v2 r2 =>
      double_zip l1 l2 + double_zip r1 r2 + v2 + tree_sum t2
    end
  end.

Definition test_double_zip : nat :=
  double_zip
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
    (Node Leaf 10 Leaf).
(** t2 = Node Leaf 10 Leaf
    Match Node/Node:
      l2=Leaf, v2=10, r2=Leaf
      double_zip (NL1L) Leaf + double_zip (NL3L) Leaf + 10 + tree_sum(NL10L)

    double_zip (NL1L) Leaf: Match Node/Leaf:
      double_zip Leaf Leaf + 1 + double_zip Leaf Leaf = 0+1+0 = 1

    double_zip (NL3L) Leaf: Match Node/Leaf:
      double_zip Leaf Leaf + 3 + double_zip Leaf Leaf = 0+3+0 = 3

    Total: 1 + 3 + 10 + 10 = 24 *)

(** TEST 5: zip with list accumulator. t2 is tree, acc is list.
    t2 non-pointer-safe due to Leaf in some calls. *)
Fixpoint zip_collect (t1 t2 : tree) (acc : list nat) : list nat :=
  match t1 with
  | Leaf => acc
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf =>
      zip_collect l1 Leaf (v1 :: zip_collect r1 Leaf acc)
    | Node l2 v2 r2 =>
      zip_collect l1 l2 (v1 :: v2 :: zip_collect r1 r2 acc)
    end
  end.

Fixpoint list_sum (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: rest => x + list_sum rest
  end.

Definition test_zip_collect : nat :=
  list_sum (zip_collect
    (Node Leaf 5 Leaf)
    (Node Leaf 10 Leaf)
    nil).
(** t1=Node Leaf 5 Leaf, t2=Node Leaf 10 Leaf
    Match Node/Node:
      l1=Leaf, l2=Leaf, v1=5, v2=10, r1=Leaf, r2=Leaf
      zip_collect Leaf Leaf (5 :: 10 :: zip_collect Leaf Leaf nil)
      = zip_collect Leaf Leaf (5 :: 10 :: nil) = [5,10]
    list_sum [5,10] = 15 *)

(** TEST 6: Three-way recursion with non-pointer-safe second tree. *)
Fixpoint merge_trees (t1 t2 : tree) : tree :=
  match t1 with
  | Leaf => t2
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => Node (merge_trees l1 Leaf) v1 (merge_trees r1 Leaf)
    | Node l2 v2 r2 =>
      Node (merge_trees l1 l2) (v1 + v2) (merge_trees r1 r2)
    end
  end.

Definition test_merge_trees : nat :=
  tree_sum (merge_trees
    (Node Leaf 5 Leaf)
    (Node Leaf 10 Leaf)).
(** t1=Node Leaf 5 Leaf, t2=Node Leaf 10 Leaf
    Match Node/Node:
      Node (merge_trees Leaf Leaf) (5+10) (merge_trees Leaf Leaf)
      = Node Leaf 15 Leaf
    tree_sum = 15 *)

(** TEST 7: Deep trees to stress the optimization. *)
Fixpoint build_balanced (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (build_balanced n') n (build_balanced n')
  end.

Definition test_deep_zip : nat :=
  zip_trees (build_balanced 5) (build_balanced 5).

(** TEST 8: Nested zip where result of one zip feeds into another. *)
Definition test_nested_zip : nat :=
  let t1 := Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf) in
  let t2 := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  zip_trees t1 t2 + zip_depth t1 t2.
(** 166 + 4 = 170 *)

End MemSafetyProbe28.

Crane Extraction "mem_safety_probe28" MemSafetyProbe28.
