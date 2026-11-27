(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Continuation-passing style — deeply nested continuations. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module CPS.

(* CPS factorial *)
Fixpoint fact_cps (n : nat) (k : nat -> nat) : nat :=
  match n with
  | 0 => k 1
  | S n' => fact_cps n' (fun r => k (S n' * r))
  end.

Definition factorial (n : nat) : nat := fact_cps n (fun x => x).

(* CPS fibonacci *)
Fixpoint fib_cps (n : nat) (k : nat -> nat) : nat :=
  match n with
  | 0 => k 0
  | 1 => k 1
  | S (S n' as n1) => fib_cps n' (fun a => fib_cps n1 (fun b => k (a + b)))
  end.

Definition fibonacci (n : nat) : nat := fib_cps n (fun x => x).

(* CPS tree fold *)
Inductive tree :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Fixpoint tree_sum_cps (t : tree) (k : nat -> nat) : nat :=
  match t with
  | Leaf n => k n
  | Node l r => tree_sum_cps l (fun sl => tree_sum_cps r (fun sr => k (sl + sr)))
  end.

Definition tree_sum (t : tree) : nat := tree_sum_cps t (fun x => x).

(* CPS list fold *)
Fixpoint sum_cps (l : list nat) (k : nat -> nat) : nat :=
  match l with
  | [] => k 0
  | x :: rest => sum_cps rest (fun r => k (x + r))
  end.

Definition list_sum (l : list nat) : nat := sum_cps l (fun x => x).

(* Double CPS — two continuations *)
Fixpoint partition_cps (p : nat -> bool) (l : list nat)
  (k : list nat -> list nat -> nat) : nat :=
  match l with
  | [] => k [] []
  | x :: rest =>
    partition_cps p rest (fun yes no =>
      if p x then k (x :: yes) no
      else k yes (x :: no))
  end.

Definition count_evens (l : list nat) : nat :=
  partition_cps Nat.even l (fun yes _ => length yes).

(* === Test values === *)

Definition test_fact_5 : nat := factorial 5.
Definition test_fib_7 : nat := fibonacci 7.
Definition test_tree : nat := tree_sum (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)).
Definition test_list_sum : nat := list_sum [10; 20; 30].
Definition test_evens : nat := count_evens [1; 2; 3; 4; 5; 6].

End CPS.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "cps" CPS.
