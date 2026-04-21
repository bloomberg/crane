From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module CpsClosureChain.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** CPS-style tree traversal that builds a deep chain of continuations.

    BUG HYPOTHESIS: Each recursive call creates a closure that captures
    [n] (from the pattern match on the current node) and [k] (the
    continuation from the caller). The chain of closures forms a
    linked-list-like structure on the heap via std::function copies.
    When the chain is finally invoked, each closure needs its captured
    [n] to still be valid.

    Unlike the fixpoint-escape tests in wip/, these are SIMPLE lambdas
    (not local fixpoints), so they should use [=] capture. The question
    is whether the [=] capture correctly copies all pattern variables,
    especially when the pattern match is on a shared_ptr type and the
    structured bindings are references. *)
Fixpoint tree_sum_cps (t : tree) (k : nat -> nat) : nat :=
  match t with
  | Leaf => k 0
  | Node l n r =>
    tree_sum_cps l (fun left_sum =>
      tree_sum_cps r (fun right_sum =>
        k (left_sum + n + right_sum)))
  end.

Definition tree_sum (t : tree) : nat :=
  tree_sum_cps t (fun x => x).

(** Build a deep tree to stress the closure chain. *)
Fixpoint build_left (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (build_left n') n Leaf
  end.

Fixpoint build_right (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node Leaf n (build_right n')
  end.

Fixpoint build_balanced (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (build_balanced n') n (build_balanced n')
  end.

(** Test: left-spine tree with 5 nodes: sum = 1+2+3+4+5 = 15 *)
Definition test_left : nat := tree_sum (build_left 5).

(** Test: right-spine tree with 5 nodes: sum = 1+2+3+4+5 = 15 *)
Definition test_right : nat := tree_sum (build_right 5).

(** Test: balanced tree depth 3: values 1,2,3 with structure
    Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 1 Leaf))
         3
         (Node (Node Leaf 1 Leaf) 2 (Node Leaf 1 Leaf))
    sum = 4*1 + 2*2 + 1*3 = 11 *)
Definition test_balanced : nat := tree_sum (build_balanced 3).

(** CPS fold: accumulates results through continuation chain.
    This creates closures that capture BOTH a pattern variable
    AND the accumulator function. *)
Fixpoint tree_fold_cps (t : tree) (base : nat) (combine : nat -> nat -> nat -> nat) (k : nat -> nat) : nat :=
  match t with
  | Leaf => k base
  | Node l n r =>
    tree_fold_cps l base combine (fun left_result =>
      tree_fold_cps r base combine (fun right_result =>
        k (combine left_result n right_result)))
  end.

(** Test: fold with multiplication: each node multiplies (left + right + n) *)
Definition test_fold : nat :=
  tree_fold_cps (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 Leaf))
                1
                (fun l n r => l + n + r)
                (fun x => x).

(** Store CPS result in a pair with another computation to test
    that the continuation chain doesn't interfere with other data. *)
Definition test_pair : nat * nat :=
  let t := build_left 4 in
  let s := tree_sum t in
  let f := tree_fold_cps t 0 (fun l n r => l + n + r) (fun x => x) in
  (s, f).

End CpsClosureChain.

Crane Extraction "cps_closure_chain" CpsClosureChain.
