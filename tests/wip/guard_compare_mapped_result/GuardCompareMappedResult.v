(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Crane Guard Compare f => true], a guard whose answer is a
    constructor of a mapped type, is accepted without complaint and emits
    an early return of [Bool::...], which names nothing -- [bool] is mapped
    to C++ [bool]: "use of undeclared identifier 'Bool'".  The guard's
    return is spelled from the constructor's Rocq name without consulting
    the mapping; either the mapping should be honoured or the directive
    rejected. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module GuardCompareMappedResult.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint eqt (a b : tree) : bool :=
  match a, b with
  | Leaf, Leaf => true
  | Node l x r, Node l' x' r' => eqt l l' && Nat.eqb x x' && eqt r r'
  | _, _ => false
  end.

Definition t1 : tree := Node (Node Leaf 1 Leaf) 2 Leaf.
Definition t2 : tree := Node (Node Leaf 1 Leaf) 2 Leaf.

Definition same : bool := eqt t1 t2.
Definition self : bool := eqt t1 t1.
Definition differ : bool := eqt t1 Leaf.

End GuardCompareMappedResult.

Crane Guard Compare GuardCompareMappedResult.eqt => true.
Crane Extraction "guard_compare_mapped_result" GuardCompareMappedResult.
