(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Higher-kinded type parameters (F : Type -> Type). *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module HigherKinded.

(* === Direct HKT parameter (not via typeclass) === *)

Definition hk_map (F : Type -> Type)
  (map_f : forall A B, (A -> B) -> F A -> F B)
  {A B : Type} (f : A -> B) (x : F A) : F B :=
  map_f A B f x.

(* === Container type with HKT === *)

Inductive Tree (A : Type) : Type :=
  | Leaf : A -> Tree A
  | Branch : Tree A -> Tree A -> Tree A.

Arguments Leaf {A} _.
Arguments Branch {A} _ _.

Fixpoint tree_map {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
  match t with
  | Leaf x => Leaf (f x)
  | Branch l r => Branch (tree_map f l) (tree_map f r)
  end.

Fixpoint tree_fold {A B : Type} (leaf_f : A -> B) (branch_f : B -> B -> B) (t : Tree A) : B :=
  match t with
  | Leaf x => leaf_f x
  | Branch l r => branch_f (tree_fold leaf_f branch_f l) (tree_fold leaf_f branch_f r)
  end.

Definition tree_sum (t : Tree nat) : nat :=
  tree_fold (fun x => x) Nat.add t.

Definition tree_size {A : Type} (t : Tree A) : nat :=
  tree_fold (fun _ => 1) Nat.add t.

(* === Apply HKT map to different containers === *)

Definition map_option {A B : Type} (f : A -> B) (o : option A) : option B :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Definition test_tree : Tree nat := Branch (Leaf 1) (Branch (Leaf 2) (Leaf 3)).
Definition test_tree_sum : nat := tree_sum test_tree.
Definition test_tree_size : nat := tree_size test_tree.
Definition test_tree_map : Tree nat := tree_map (fun n => n * 2) test_tree.
Definition test_hk_option : option nat := hk_map option (@map_option) (fun n => n + 1) (Some 5).
Definition test_hk_tree : Tree nat := hk_map Tree (@tree_map) (fun n => n + 10) test_tree.

End HigherKinded.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "higher_kinded" HigherKinded.
