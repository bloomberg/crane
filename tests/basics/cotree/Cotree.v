(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Coinductive rose trees — cotree with colist children. *)
(* Inspired by bloomberg/game-trees (Korkut, CPP'26). *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module Cotree.

(* === Coinductive types === *)

CoInductive colist (A : Type) : Type :=
| conil : colist A
| cocons : A -> colist A -> colist A.

Arguments conil {A}.
Arguments cocons {A} x xs.

CoInductive cotree (A : Type) : Type :=
| conode : A -> colist (cotree A) -> cotree A.

Arguments conode {A} a f.

(* === Inductive tree for finite approximation === *)

Inductive tree (A : Type) : Type :=
| node : A -> list (tree A) -> tree A.

Arguments node {A} a children.

(* === Basic accessors === *)

Definition root {A : Type} (t : cotree A) : A :=
  match t with
  | conode a _ => a
  end.

Definition children {A : Type} (t : cotree A) : colist (cotree A) :=
  match t with
  | conode _ f => f
  end.

Definition tree_root {A : Type} (t : tree A) : A :=
  match t with
  | node a _ => a
  end.

(* === Corecursive operations === *)

Definition comap {A B : Type} (f : A -> B) : colist A -> colist B :=
  cofix comap (l : colist A) : colist B :=
    match l with
    | conil => conil
    | cocons x xs => cocons (f x) (comap xs)
    end.

CoFixpoint comap_cotree {A B : Type} (g : A -> B) (t : cotree A) : cotree B :=
  match t with
  | conode a f => conode (g a) (comap (comap_cotree g) f)
  end.

Definition singleton_cotree {A : Type} (a : A) : cotree A :=
  conode a conil.

(* Build infinite game tree from state transition function *)
CoFixpoint unfold_cotree {A : Type} (next : A -> colist A) (init : A) : cotree A :=
  conode init (comap (unfold_cotree next) (next init)).

(* === Fuel-based finite approximations === *)

Fixpoint list_of_colist {A : Type} (fuel : nat) (l : colist A)
  {struct fuel} : list A :=
  match fuel with
  | O => nil
  | S fuel' =>
    match l with
    | conil => nil
    | cocons x xs => cons x (list_of_colist fuel' xs)
    end
  end.

Fixpoint tree_of_cotree {A : Type} (fuel : nat) (t : cotree A)
  {struct fuel} : tree A :=
  match t with
  | conode a f =>
    match fuel with
    | O => node a []
    | S fuel' =>
        node a (map (tree_of_cotree fuel') (list_of_colist fuel f))
    end
  end.

(* Tree size via nested fix for nested inductive *)
Fixpoint tree_size {A : Type} (t : tree A) : nat :=
  match t with
  | node _ cs =>
      S ((fix aux (l : list (tree A)) : nat :=
            match l with
            | nil => 0
            | cons t' rest => tree_size t' + aux rest
            end) cs)
  end.

(* === Test values === *)

(* Manual finite cotree: node 1 [node 2 [], node 3 []] *)
Definition sample_cotree : cotree nat :=
  conode 1 (cocons (singleton_cotree 2) (cocons (singleton_cotree 3) conil)).

Definition test_root : nat := root sample_cotree.

Definition test_doubled_root : nat :=
  root (comap_cotree (fun n => n * 2) sample_cotree).

(* Infinite stream of naturals *)
CoFixpoint nats (n : nat) : colist nat := cocons n (nats (S n)).

Definition test_first_five : list nat := list_of_colist 5 (nats 0).

(* Binary counting tree: each n has children [2n+1, 2n+2] *)
Definition binary_children (n : nat) : colist nat :=
  cocons (2 * n + 1) (cocons (2 * n + 2) conil).

Definition binary_tree : cotree nat := unfold_cotree binary_children 0.

Definition test_binary_root : nat := root binary_tree.

(* Finite approximation with depth 2 *)
Definition test_approx : tree nat := tree_of_cotree 2 binary_tree.
Definition test_approx_root : nat := tree_root test_approx.
Definition test_approx_size : nat := tree_size test_approx.

End Cotree.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "cotree" Cotree.
