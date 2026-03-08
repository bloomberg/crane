(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral: base_for_next1 and base_for_next2 cross page boundary at PC=255. *)

From Stdlib Require Import Nat.

Module BaseForNextPageCross.

Record state : Type := mkState {
  pc : nat
}.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition pc_inc1 (s : state) : nat := addr12_of_nat (pc s + 1).
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).
Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.

(* base_for_next1 crosses page boundary at PC=255 *)
Definition base_for_next1 (s : state) : nat := page_base (pc_inc1 s).

(* base_for_next2 crosses page boundary at PC=255 *)
Definition base_for_next2 (s : state) : nat := page_base (pc_inc2 s).

Definition test_next1 : nat := base_for_next1 (mkState 255).
Definition test_next2 : nat := base_for_next2 (mkState 255).

Definition t : nat * nat := (test_next1, test_next2).

End BaseForNextPageCross.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "base_for_next_page_cross" BaseForNextPageCross.
