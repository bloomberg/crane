From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NestedPartialApp.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** 3-argument function: builds Node(t1, n, t2). *)
Definition build_node (t1 : tree) (n : nat) (t2 : tree) : tree :=
  Node t1 n t2.

(** BUG HYPOTHESIS: Partially apply build_node in stages.
    g = build_node t1  → closure captures t1
    h = g 42           → closure captures t1 and 42
    Then invoke h twice with different args.
    If captures are moved, second invocation fails.

    Expected:
      t1 = Node Leaf 10 Leaf (sum = 10)
      h c1 = Node(t1, 42, c1)
      h c2 = Node(t1, 42, c2)
      tree_sum(h c1) + tree_sum(h c2) where c1=Node Leaf 1 Leaf, c2=Node Leaf 2 Leaf
      = (10 + 42 + 1) + (10 + 42 + 2) = 53 + 54 = 107 *)
Definition nested_partial_bug : nat :=
  let t1 := Node Leaf 10 Leaf in
  let g := build_node t1 in
  let h := g 42 in
  let r1 := h (Node Leaf 1 Leaf) in
  let r2 := h (Node Leaf 2 Leaf) in
  tree_sum r1 + tree_sum r2.

(** Variation: use intermediate partial app g twice before further
    partial application. Tests if g's capture of t1 survives. *)
Definition nested_partial_reuse : nat :=
  let t1 := Node Leaf 10 Leaf in
  let g := build_node t1 in
  let h1 := g 42 in
  let h2 := g 99 in
  let r1 := h1 (Node Leaf 1 Leaf) in
  let r2 := h2 (Node Leaf 2 Leaf) in
  tree_sum r1 + tree_sum r2.

(** Variation: 4-argument function, triple nesting. *)
Definition quad_fn (a : tree) (b : nat) (c : nat) (d : tree) : nat :=
  tree_sum a + b + c + tree_sum d.

Definition triple_partial : nat :=
  let t := Node Leaf 10 Leaf in
  let f1 := quad_fn t in
  let f2 := f1 20 in
  let f3 := f2 30 in
  let r1 := f3 (Node Leaf 1 Leaf) in
  let r2 := f3 (Node Leaf 2 Leaf) in
  r1 + r2.

End NestedPartialApp.

Crane Extraction "nested_partial_app" NestedPartialApp.
