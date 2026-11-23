(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Mutual inductives with indices (not just parameters). *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module MutualIndexed.

(* Even/Odd as mutual inductives indexed by nat *)
Inductive Even : nat -> Prop :=
  | even_O : Even 0
  | even_S : forall n, Odd n -> Even (S n)
with Odd : nat -> Prop :=
  | odd_S : forall n, Even n -> Odd (S n).

(* Mutual inductives with computational content (not Prop) *)
Inductive EvenTree : nat -> Type :=
  | ELeaf : EvenTree 0
  | ENode : forall n, nat -> OddTree n -> EvenTree (S n)
with OddTree : nat -> Type :=
  | ONode : forall n, nat -> EvenTree n -> OddTree (S n).

Definition even_val {n : nat} (t : EvenTree n) : nat :=
  match t with
  | ELeaf => 0
  | ENode _ v _ => v
  end.

Definition odd_val {n : nat} (t : OddTree n) : nat :=
  match t with
  | ONode _ v _ => v
  end.

(* Build a small tree *)
Definition leaf : EvenTree 0 := ELeaf.
Definition tree1 : OddTree 1 := ONode 0 10 ELeaf.
Definition tree2 : EvenTree 2 := ENode 1 20 (ONode 0 10 ELeaf).

Definition test_leaf_val : nat := even_val leaf.
Definition test_tree1_val : nat := odd_val tree1.
Definition test_tree2_val : nat := even_val tree2.

End MutualIndexed.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "mutual_indexed" MutualIndexed.
