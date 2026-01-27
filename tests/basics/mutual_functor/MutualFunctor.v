(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Test: Mutually inductive types inside a functor *)

From Stdlib Require Import NArith.
Open Scope nat_scope.

(* Module type for elements *)
Module Type Elem.
  Parameter t : Type.
  Parameter dflt : t.  (* 'default' is a C++ reserved keyword, use 'dflt' *)
End Elem.

(* Functor with mutually inductive types *)
Module MutualTree (E : Elem).
  (* Mutually inductive: forest and tree *)
  Inductive tree : Type :=
  | Leaf : nat -> tree      (* Use nat to avoid E.t in recursors *)
  | Node : nat -> forest -> tree
  with forest : Type :=
  | FNil : forest
  | FCons : tree -> forest -> forest.

  (* Mutual recursion over the types *)
  Fixpoint tree_size (t : tree) : nat :=
    match t with
    | Leaf _ => 1
    | Node _ f => 1 + forest_size f
    end
  with forest_size (f : forest) : nat :=
    match f with
    | FNil => 0
    | FCons t rest => tree_size t + forest_size rest
    end.

  Fixpoint tree_sum (t : tree) : nat :=
    match t with
    | Leaf n => n
    | Node n f => n + forest_sum f
    end
  with forest_sum (f : forest) : nat :=
    match f with
    | FNil => 0
    | FCons t rest => tree_sum t + forest_sum rest
    end.

  (* Example values - use E.dflt converted to nat somehow *)
  Definition leaf1 : tree := Leaf 1.
  Definition leaf2 : tree := Leaf 2.
  Definition small_forest : forest := FCons leaf1 (FCons leaf2 FNil).
  Definition sample_tree : tree := Node 0 small_forest.
End MutualTree.

(* Concrete element module *)
Module NatElem : Elem.
  Definition t := nat.
  Definition dflt := 0.
End NatElem.

(* Instantiate the functor *)
Module NatTree := MutualTree NatElem.

(* Test values *)
Definition test_tree_size := NatTree.tree_size NatTree.sample_tree.
Definition test_forest_size := NatTree.forest_size NatTree.small_forest.
Definition test_tree_sum := NatTree.tree_sum NatTree.sample_tree.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction "mutual_functor" test_tree_size test_forest_size test_tree_sum.
