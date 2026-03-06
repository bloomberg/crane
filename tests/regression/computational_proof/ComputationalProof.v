(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Computational proofs — Defined proofs used at runtime. *)

From Stdlib Require Import Nat Bool List Lia.
Import ListNotations.

Module ComputationalProof.

(* Decision procedure that computes *)
Definition nat_eq_dec (n m : nat) : {n = m} + {n <> m}.
Proof.
  decide equality.
Defined.

(* Boolean decision from sumbool *)
Definition nat_eqb_dec (n m : nat) : bool :=
  if nat_eq_dec n m then true else false.

(* le is decidable *)
Definition le_dec (n m : nat) : {n <= m} + {m < n}.
Proof.
  induction n as [|n' IHn'] in m |- *.
  - left. lia.
  - destruct m.
    + right. lia.
    + destruct (IHn' m).
      * left. lia.
      * right. lia.
Defined.

Definition nat_leb_dec (n m : nat) : bool :=
  if le_dec n m then true else false.

(* Minimum via decision procedure *)
Definition min_dec (n m : nat) : nat :=
  if le_dec n m then n else m.

(* Maximum via decision procedure *)
Definition max_dec (n m : nat) : nat :=
  if le_dec n m then m else n.

(* Insertion sort using decidable le *)
Fixpoint insert_dec (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => [x]
  | y :: rest =>
      if le_dec x y then x :: y :: rest
      else y :: insert_dec x rest
  end.

Fixpoint isort_dec (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: rest => insert_dec x (isort_dec rest)
  end.

(* Test values *)
Definition test_eq_true : bool := nat_eqb_dec 5 5.
Definition test_eq_false : bool := nat_eqb_dec 3 7.
Definition test_leb_true : bool := nat_leb_dec 3 5.
Definition test_leb_false : bool := nat_leb_dec 8 2.
Definition test_min : nat := min_dec 4 9.
Definition test_max : nat := max_dec 4 9.
Definition test_sort : list nat := isort_dec [5; 1; 4; 2; 3].

End ComputationalProof.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "computational_proof" ComputationalProof.
