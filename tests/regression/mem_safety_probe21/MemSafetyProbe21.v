From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe21.

(** Probe 21: Loopified recursion with constructed-value arguments.

    Attack vectors:
    1. Recursive calls where the tree argument is a CONSTRUCTOR CALL
       (not the same parameter). The loopifier stores raw pointers to
       tree parameters. If the recursive call creates a temporary tree,
       the pointer to the temporary may dangle after the temporary dies.
    2. Non-tail recursive calls where both the original parameter AND
       a constructed tree are used, requiring frame saves and moves. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 1: Tail-recursive function where the recursive call takes
    a constructed tree. The loopifier must store the new tree
    somewhere that outlives the iteration. *)
Fixpoint grow_and_sum (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' => grow_and_sum (Node t n Leaf) n'
  end.

Definition test_grow_and_sum : nat :=
  grow_and_sum Leaf 3.
(** grow_and_sum Leaf 3
    = grow_and_sum (Node Leaf 3 Leaf) 2
    = grow_and_sum (Node (Node Leaf 3 Leaf) 2 Leaf) 1
    = grow_and_sum (Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf) 0
    = tree_sum (Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf)
    = 3 + 2 + 1 = 6 *)

(** TEST 2: Non-tail recursive with constructed tree argument.
    The recursive call creates a new tree AND uses the original. *)
Fixpoint double_grow (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' => tree_sum t + double_grow (Node t 0 Leaf) n'
  end.

Definition test_double_grow : nat :=
  double_grow (Node Leaf 5 Leaf) 2.
(** double_grow (Node Leaf 5 Leaf) 2
    = tree_sum(NL5L) + double_grow (Node (NL5L) 0 Leaf) 1
    = 5 + (tree_sum(Node(NL5L)0L) + double_grow (Node (Node(NL5L)0L) 0 Leaf) 0)
    = 5 + (5 + tree_sum(Node(Node(NL5L)0L)0L))
    = 5 + (5 + 5)
    = 15 *)

(** TEST 3: Two recursive calls, one with original tree, one with
    constructed tree. *)
Fixpoint branch_grow (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' => branch_grow t n' + branch_grow (Node Leaf n Leaf) n'
  end.

Definition test_branch_grow : nat :=
  branch_grow (Node Leaf 10 Leaf) 2.
(** branch_grow (NL10L) 2
    = branch_grow (NL10L) 1 + branch_grow (NL2L) 1
    = (branch_grow (NL10L) 0 + branch_grow (NL1L) 0)
      + (branch_grow (NL2L) 0 + branch_grow (NL1L) 0)
    = (10 + 1) + (2 + 1)
    = 14 *)

(** TEST 4: Recursive call where the tree argument is built from
    MULTIPLE constructor calls with the original tree embedded. *)
Fixpoint embed_grow (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' => embed_grow (Node (Node t n Leaf) 0 (Node Leaf n t)) n'
  end.

Definition test_embed_grow : nat :=
  embed_grow Leaf 2.
(** embed_grow Leaf 2
    = embed_grow (Node (Node Leaf 2 Leaf) 0 (Node Leaf 2 Leaf)) 1
    Let t1 = Node (Node Leaf 2 Leaf) 0 (Node Leaf 2 Leaf), sum = 2+0+2 = 4
    = embed_grow (Node (Node t1 1 Leaf) 0 (Node Leaf 1 t1)) 0
    Let t2 = Node (Node t1 1 Leaf) 0 (Node Leaf 1 t1)
    sum t2 = (sum t1 + 1 + 0) + 0 + (0 + 1 + sum t1) = (4+1) + (1+4) = 10
    = tree_sum t2 = 10 *)

(** TEST 5: Accumulator pattern with tree building. *)
Fixpoint accum_tree (acc : tree) (n : nat) : tree :=
  match n with
  | O => acc
  | S n' => accum_tree (Node acc n Leaf) n'
  end.

Definition test_accum_tree : nat :=
  tree_sum (accum_tree Leaf 4).
(** accum_tree Leaf 4
    = accum_tree (Node Leaf 4 Leaf) 3
    = accum_tree (Node (Node Leaf 4 Leaf) 3 Leaf) 2
    = accum_tree (Node (Node (Node Leaf 4 Leaf) 3 Leaf) 2 Leaf) 1
    = accum_tree (Node (Node (Node (Node Leaf 4 Leaf) 3 Leaf) 2 Leaf) 1 Leaf) 0
    = Node (Node (Node (Node Leaf 4 Leaf) 3 Leaf) 2 Leaf) 1 Leaf
    tree_sum = 4 + 3 + 2 + 1 = 10 *)

(** TEST 6: CPS-like pattern where the continuation builds a tree. *)
Fixpoint cps_sum (t : tree) (k : nat -> nat) : nat :=
  match t with
  | Leaf => k 0
  | Node l v r =>
    cps_sum l (fun lsum => cps_sum r (fun rsum => k (lsum + v + rsum)))
  end.

Definition test_cps_sum : nat :=
  cps_sum (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) (fun n => n).
(** Should equal tree_sum = 1 + 2 + 3 = 6 *)

(** TEST 7: Mutually-referencing recursive call with tree
    construction at each level. *)
Fixpoint weave (t1 t2 : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t1 + tree_sum t2
  | S n' => weave (Node t2 n Leaf) (Node t1 n Leaf) n'
  end.

Definition test_weave : nat :=
  weave (Node Leaf 1 Leaf) (Node Leaf 2 Leaf) 2.
(** weave (NL1L) (NL2L) 2
    = weave (Node (NL2L) 2 Leaf) (Node (NL1L) 2 Leaf) 1
    Let a = Node(NL2L)2L, sum_a=2+2=4; b = Node(NL1L)2L, sum_b=1+2=3
    = weave (Node b 1 Leaf) (Node a 1 Leaf) 0
    Let c = Node(b)1L, sum_c=3+1=4; d = Node(a)1L, sum_d=4+1=5
    = sum_c + sum_d = 4 + 5 = 9 *)

(** TEST 8: Deep nesting with tree_sum at each level before recursion. *)
Fixpoint sum_and_grow (t : tree) (n : nat) : nat :=
  match n with
  | O => tree_sum t
  | S n' =>
    let s := tree_sum t in
    s + sum_and_grow (Node t s Leaf) n'
  end.

Definition test_sum_and_grow : nat :=
  sum_and_grow (Node Leaf 1 Leaf) 3.
(** sum_and_grow (NL1L) 3
    s=1. 1 + sum_and_grow (Node(NL1L)1L) 2
    s=1+1=2. 1 + 2 + sum_and_grow (Node(Node(NL1L)1L)2L) 1
    s=1+1+2=4. 1 + 2 + 4 + sum_and_grow (Node(Node(Node(NL1L)1L)2L)4L) 0
    = 1 + 2 + 4 + (1+1+2+4) = 7 + 8 = 15 *)

End MemSafetyProbe21.

Crane Extraction "mem_safety_probe21" MemSafetyProbe21.
