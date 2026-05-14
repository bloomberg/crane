From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe23.

(** Probe 23: Owned-parameter loopification with child recursion.

    Attack vector: Make the tree parameter OWNED (by value) by having
    the function return or store the original tree, while ALSO recursing
    on the tree's children. If the loopifier stores the tree by value in
    Enter frames AND stores raw pointers to children in After frames
    (because children flow to pointer-safe positions), the raw pointers
    dangle when the Enter frame's tree goes out of scope.

    Secondary: test interactions between loop variable reuse, clone
    correctness, and move semantics for complex value types. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Fixpoint tree_size (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l _ r => 1 + tree_size l + tree_size r
  end.

(** TEST 1: Return the ORIGINAL tree alongside recursive child processing.
    t escapes because it is returned. Recursive calls on l and r (children).
    Loopifier must handle: owned param + pointer-safe children. *)
Fixpoint sum_with_original (t : tree) : tree * nat :=
  match t with
  | Leaf => (Leaf, 0)
  | Node l v r =>
    let pl := sum_with_original l in
    let pr := sum_with_original r in
    (t, snd pl + v + snd pr)
  end.

Definition test_sum_with_original : nat :=
  let r := sum_with_original
    (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  snd r + tree_sum (fst r).
(** snd = 3 + 7 + 11 = 21; fst = original tree, sum = 21; total = 42 *)

(** TEST 2: Return a PAIR of the original tree and a transformed copy.
    Forces tree to be owned; two recursive calls on children. *)
Fixpoint dup_and_double (t : tree) : tree * tree :=
  match t with
  | Leaf => (Leaf, Leaf)
  | Node l v r =>
    let pl := dup_and_double l in
    let pr := dup_and_double r in
    (t, Node (snd pl) (v * 2) (snd pr))
  end.

Definition test_dup_and_double : nat :=
  let r := dup_and_double
    (Node (Node Leaf 3 Leaf) 5 (Node Leaf 7 Leaf)) in
  tree_sum (fst r) + tree_sum (snd r).
(** fst = original = 3+5+7=15; snd = doubled = 6+10+14=30; total=45 *)

(** TEST 3: Store children in result alongside recursive processing.
    l and r are extracted from match, BOTH used in result AND in
    recursive calls. Tests whether children are correctly cloned when
    they appear in both continuation and recursive positions. *)
Fixpoint collect_children (t : tree) : tree * tree * nat :=
  match t with
  | Leaf => (Leaf, Leaf, 0)
  | Node l v r =>
    let pl := collect_children l in
    let pr := collect_children r in
    let s := match pl with (_, _, n) => n end
             + v
             + match pr with (_, _, n) => n end in
    (l, r, s)
  end.

Definition test_collect_children : nat :=
  let r := collect_children
    (Node (Node Leaf 2 Leaf) 5 (Node Leaf 8 Leaf)) in
  match r with
  | (left_child, right_child, s) =>
    tree_sum left_child + tree_sum right_child + s
  end.
(** s = 2+5+8=15; left_child = Node Leaf 2 Leaf, sum=2;
    right_child = Node Leaf 8 Leaf, sum=8; total=25 *)

(** TEST 4: Recursive function that rebuilds tree with an
    ACCUMULATOR that captures the original tree. The accumulator
    forces the tree to be owned. Two recursive calls on children. *)
Fixpoint sum_with_acc (t : tree) (acc : nat) : tree * nat :=
  match t with
  | Leaf => (Leaf, acc)
  | Node l v r =>
    let pl := sum_with_acc l (acc + v) in
    let pr := sum_with_acc r (snd pl) in
    (Node (fst pl) v (fst pr), snd pr)
  end.

Definition test_sum_with_acc : nat :=
  let r := sum_with_acc
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 0 in
  snd r + tree_sum (fst r).
(** Accumulator trace: start 0, +2=2, left(+1=3, leaf=3), right(+3=6, leaf=6)
    snd = 6; tree_sum of rebuilt tree = 1+2+3=6; total=12 *)

(** TEST 5: Function using tree_sum on children INSIDE the same
    expression as recursive calls. Tests that child pointers remain
    valid when other operations happen on the same tree. *)
Fixpoint interleaved_ops (t : tree) : nat * nat :=
  match t with
  | Leaf => (0, 0)
  | Node l v r =>
    let sl := tree_sum l in
    let sr := tree_sum r in
    let pl := interleaved_ops l in
    let pr := interleaved_ops r in
    (sl + v + sr, fst pl + v + fst pr)
  end.

Definition test_interleaved_ops : nat :=
  let r := interleaved_ops
    (Node (Node Leaf 2 Leaf) 5 (Node Leaf 3 Leaf)) in
  fst r + snd r.
(** fst: tree_sum l + v + tree_sum r = 2+5+3=10
    snd: fst(interleaved_ops l) + v + fst(interleaved_ops r)
       = (tree_sum Leaf + 2 + tree_sum Leaf) + 5
         + (tree_sum Leaf + 3 + tree_sum Leaf)
       = (0+2+0) + 5 + (0+3+0) = 10
    total = 20 *)

(** TEST 6: Nested tree type — tree of trees. Tests clone correctness
    for deeply nested value types. *)
Fixpoint flatten_tree_of_trees (t : tree) (inner : tree) : nat :=
  match t with
  | Leaf => tree_sum inner
  | Node l v r =>
    let new_inner := Node inner v Leaf in
    flatten_tree_of_trees l new_inner + flatten_tree_of_trees r inner
  end.

Definition test_flatten_tree_of_trees : nat :=
  flatten_tree_of_trees
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
    (Node Leaf 10 Leaf).
(** At root: inner = Node Leaf 10 Leaf
    new_inner = Node (Node Leaf 10 Leaf) 2 Leaf
    Left child (Node Leaf 1 Leaf):
      new_inner2 = Node new_inner 1 Leaf = Node (Node (NL10L) 2 Leaf) 1 Leaf
      Left leaf: tree_sum new_inner2 = 10+2+1 = 13
      Right leaf: tree_sum new_inner = 10+2 = 12
      Subtotal: 13+12 = 25
    Right child (Node Leaf 3 Leaf):
      new_inner3 = Node inner 3 Leaf = Node (NL10L) 3 Leaf
      Left leaf: tree_sum new_inner3 = 10+3 = 13
      Right leaf: tree_sum inner = 10
      Subtotal: 13+10 = 23
    Total: 25+23 = 48 *)

(** TEST 7: Two recursive calls where one takes a CONSTRUCTED tree
    with t embedded AND another takes a child of t.
    Forces t to NOT be pointer-safe. The After frame saves
    state for the child-based call. *)
Fixpoint mixed_recurse (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' =>
    match t with
    | Leaf => 0
    | Node l v r =>
      mixed_recurse (Node t v Leaf) n' + mixed_recurse r n'
    end
  end.

Definition test_mixed_recurse : nat :=
  mixed_recurse (Node Leaf 5 Leaf) 1.
(** mixed_recurse (Node Leaf 5 Leaf) 1
    = mixed_recurse (Node (Node Leaf 5 Leaf) 5 Leaf) 0
      + mixed_recurse Leaf 0
    = tree_sum (Node (Node Leaf 5 Leaf) 5 Leaf) + tree_sum Leaf
    = (5+5) + 0 = 10 *)

(** TEST 8: Three-way split: function returns original tree AND
    uses tree_size on children. Forces tree owned; exercises
    the interplay between clone, move, and raw pointer in
    continuation frames. *)
Fixpoint annotate_sizes (t : tree) : tree * nat :=
  match t with
  | Leaf => (Leaf, 0)
  | Node l v r =>
    let sl := tree_size l in
    let sr := tree_size r in
    let pl := annotate_sizes l in
    let pr := annotate_sizes r in
    (Node (fst pl) (v + sl + sr) (fst pr), snd pl + snd pr + 1)
  end.

Definition test_annotate_sizes : nat :=
  let r := annotate_sizes
    (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) in
  tree_sum (fst r) + snd r.
(** Left leaf: (Leaf,0) Right leaf: (Leaf,0)
    Left (Node Leaf 10 Leaf): sl=1, sr=1, annotate -> (Node Leaf (10+1+1) Leaf, 0+0+1) = (NL12L, 1)
    Right (Node Leaf 30 Leaf): sl=1, sr=1, annotate -> (Node Leaf (30+1+1) Leaf, 0+0+1) = (NL32L, 1)
    Root: sl=3, sr=3, annotate -> (Node (NL12L) (20+3+3) (NL32L), 1+1+1) = (Node(NL12L) 26 (NL32L), 3)
    tree_sum of fst = 12+26+32 = 70; snd = 3; total = 73 *)

End MemSafetyProbe23.

Crane Extraction "mem_safety_probe23" MemSafetyProbe23.
