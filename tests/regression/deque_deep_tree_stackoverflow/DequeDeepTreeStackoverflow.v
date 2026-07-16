(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   WIP test: demonstrate stack overflow in destructor for rose trees
   when list is mapped to std::deque via DequeList.

   The issue: with DequeList, the iterative destructor does NOT drain
   the deque field (since it's an inline-custom list type). When a rose
   tree is deeply nested (each node has exactly one child in its deque),
   destruction follows:
     ~RoseTree() -> member destruction -> ~shared_ptr<deque<RoseTree>>()
       -> ~deque<RoseTree>() -> ~RoseTree() for each element -> ...

   The recursion depth equals the tree depth. For a tree of depth 100K+,
   this overflows the C++ call stack.
*)
From Crane Require Import Mapping.NatIntStd Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

Module DequeDeepTreeStackoverflow.

Inductive rose : Type :=
| RLeaf : nat -> rose
| RNode : list rose -> rose.

(* Build a deeply nested tree: each level has one child *)
Fixpoint deep_tree (depth : nat) : rose :=
  match depth with
  | O => RLeaf 42
  | S n => RNode (cons (deep_tree n) nil)
  end.

(* Force construction and destruction of a deep tree *)
Definition test_deep (n : nat) : nat :=
  match deep_tree n with
  | RLeaf x => x
  | RNode _ => 0
  end.

End DequeDeepTreeStackoverflow.

Set Crane Loopify.
Crane Extraction "deque_deep_tree_stackoverflow" DequeDeepTreeStackoverflow.
