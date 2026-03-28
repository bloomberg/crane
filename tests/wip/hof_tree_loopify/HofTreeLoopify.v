(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Higher-order functions on trees with multi-recursion.

   These functions take function parameters AND have multiple recursive calls
   per branch. This combination defeats loopification because:
   1. Function params become C++ template parameters (F0&&)
   2. Multi-recursion requires frame-based loopification
   3. The combine operation involves constructors with saved expressions
      (e.g., Node(left_result, f(x), right_result)), which find_combine_op
      in loopify.ml can't decompose (dd_saved != [])

   As a result, these functions keep C++ stack recursion and will stack-overflow
   on deep trees.

   See translation.ml:5985:
     "TODO: below is needed for lambdas in recursive positions, but is badddddd."
*)
From Stdlib Require Import List Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Set Crane Loopify.

Module HofTreeLoopify.

Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} l x r.

(* Build a maximally deep left-leaning tree of given depth.
   depth_tree 100000 creates a tree with 100000 left-nested nodes,
   which requires 100000 stack frames if traversed recursively. *)
Fixpoint depth_tree (n : nat) : tree nat :=
  match n with
  | O => leaf
  | S m => node (depth_tree m) n leaf
  end.

(* ===================================================================== *)
(* Pattern 1: tree_map                                                    *)
(*   Two recursive calls + function param applied to node value.          *)
(*   The combine operation is: Node(left_result, f(x), right_result)      *)
(*   This has a saved expression (f x) between the two recursive calls,   *)
(*   which prevents find_combine_op from decomposing it.                  *)
(* ===================================================================== *)
Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | leaf => leaf
  | node l x r => node (tree_map f l) (f x) (tree_map f r)
  end.

(* ===================================================================== *)
(* Pattern 2: tree_fold                                                   *)
(*   Two recursive calls + function param combining all three values.     *)
(*   The combine operation is: f_node(left_result, x, right_result)       *)
(*   Even harder than tree_map because the combine itself is the HOF.     *)
(* ===================================================================== *)
Fixpoint tree_fold {A B : Type} (base : B) (f : B -> A -> B -> B)
                   (t : tree A) : B :=
  match t with
  | leaf => base
  | node l x r => f (tree_fold base f l) x (tree_fold base f r)
  end.

(* ===================================================================== *)
(* Pattern 3: tree_zip_with                                               *)
(*   Two recursive calls + function param combining values from two trees *)
(*   Combines two trees element-wise, like Tree.merge but with a HOF.     *)
(* ===================================================================== *)
Fixpoint tree_zip_with {A B C : Type} (f : A -> B -> C)
                       (t1 : tree A) (t2 : tree B) : tree C :=
  match t1, t2 with
  | node l1 x1 r1, node l2 x2 r2 =>
      node (tree_zip_with f l1 l2) (f x1 x2) (tree_zip_with f r1 r2)
  | _, _ => leaf
  end.

(* ===================================================================== *)
(* Pattern 4: tree_map_accum                                              *)
(*   Two recursive calls + accumulator threaded through function param.   *)
(*   The function f takes an accumulator AND a node value, returning      *)
(*   both a new accumulator and a transformed value.                      *)
(*   This is the hardest pattern: the accumulator changes at each call    *)
(*   AND there are two recursive calls AND a function parameter.          *)
(* ===================================================================== *)
Fixpoint tree_map_accum {A B S : Type} (f : S -> A -> S * B)
                        (acc : S) (t : tree A) : S * tree B :=
  match t with
  | leaf => (acc, leaf)
  | node l x r =>
      let '(acc1, l') := tree_map_accum f acc l in
      let '(acc2, x') := f acc1 x in
      let '(acc3, r') := tree_map_accum f acc2 r in
      (acc3, node l' x' r')
  end.

(* ===================================================================== *)
(* Concrete test instances                                                *)
(* ===================================================================== *)

Definition small_tree := node (node (node leaf 1 leaf) 2 (node leaf 3 leaf))
                              4
                              (node (node leaf 5 leaf) 6 (node leaf 7 leaf)).

Definition mapped := tree_map (fun x => x * 2) small_tree.
Definition folded := tree_fold 0 (fun l x r => l + x + r) small_tree.
Definition zipped := tree_zip_with Nat.add small_tree small_tree.
Definition accum := tree_map_accum (fun s x => (s + x, s)) 0 small_tree.

(* Deep tree for stack overflow test.
   If loopified correctly: works fine (iterative).
   If not loopified: stack overflow on tree_map/tree_fold. *)
Definition deep := depth_tree 50000.

End HofTreeLoopify.

Crane Extraction "hof_tree_loopify" HofTreeLoopify.
