(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: page/address arithmetic. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PageAddress.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.

Definition page_of (p : nat) : nat :=
  addr12_of_nat p / 256.

Definition page_base (p : nat) : nat :=
  page_of p * 256.

Definition branch_target (pc off : nat) : nat :=
  page_base (addr12_of_nat (pc + 2)) + (off mod 256).

Definition p_small : nat := 777.
Definition p_same : nat := 600.
Definition p_cross_254 : nat := 254.
Definition p_cross_255 : nat := 255.

Definition page_base_777 : nat := page_base 777.
Definition branch_example : nat := branch_target 100 42.

End PageAddress.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "page_address" PageAddress.
