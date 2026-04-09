From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module FoldClosureAccum.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** Sum all values in a tree. *)
Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** Build a composed function by folding over a list of trees.
    Each step takes the accumulated function and the current tree,
    producing a new function that adds tree_sum of the current tree
    to the accumulated function's result.

    BUG HYPOTHESIS: Each fold step creates a closure [&acc, &t] that
    captures the previous closure (acc) and the current tree (t).
    If captures are by reference, the previous closure is stack-local
    and dies when the fold step returns, creating a dangling chain. *)
Definition compose_adders (trees : list tree) : nat -> nat :=
  fold_right
    (fun (t : tree) (acc : nat -> nat) =>
       fun x => acc x + tree_sum t)
    (fun x => x)
    trees.

(** Test: compose adders from 3 trees.
    t1 sums to 10, t2 sums to 20, t3 sums to 30.
    compose_adders [t1; t2; t3] x = x + 30 + 20 + 10 = x + 60
    Expected: compose_adders [t1; t2; t3] 0 = 60 *)
Definition fold_bug : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let t3 := Node Leaf 30 Leaf in
  let f := compose_adders (t1 :: t2 :: t3 :: nil) in
  f 0.

(** Test with non-zero starting value.
    Expected: compose_adders [t1; t2; t3] 7 = 67 *)
Definition fold_bug_offset : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let t3 := Node Leaf 30 Leaf in
  let f := compose_adders (t1 :: t2 :: t3 :: nil) in
  f 7.

(** Invoke the composed function twice — tests if closures survive
    multiple invocations. *)
Definition fold_bug_double : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f := compose_adders (t1 :: t2 :: nil) in
  f 0 + f 100.

End FoldClosureAccum.

Crane Extraction "fold_closure_accum" FoldClosureAccum.
