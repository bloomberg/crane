(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: page-base computations for next-PC addresses. *)

From Stdlib Require Import Nat.

Module PageBaseNextPc.

Record state : Type := mkState {
  pc : nat
}.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.

Definition pc_inc1 (s : state) : nat := addr12_of_nat (pc s + 1).
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).

Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.

Definition base_for_next1 (s : state) : nat := page_base (pc_inc1 s).
Definition base_for_next2 (s : state) : nat := page_base (pc_inc2 s).

Definition t : nat :=
  let s := mkState 511 in
  base_for_next1 s + base_for_next2 s.

End PageBaseNextPc.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "page_base_next_pc" PageBaseNextPc.
