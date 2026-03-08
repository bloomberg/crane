(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral: even/odd registers index the same pair as successor/predecessor. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RegPairSuccessor.

Record state : Type := mkState { regs : list nat }.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition sample : state := mkState [0; 0; 10; 11; 0; 0].

(* Even register indexes the same pair as its successor *)
Definition even_same_as_successor : bool :=
  Nat.eqb (get_reg_pair sample 2) (get_reg_pair sample 3).

(* Odd register indexes the same pair as its predecessor *)
Definition odd_same_as_predecessor : bool :=
  Nat.eqb (get_reg_pair sample 3) (get_reg_pair sample 2).

Definition t : bool := even_same_as_successor && odd_same_as_predecessor.

End RegPairSuccessor.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "reg_pair_successor" RegPairSuccessor.
