(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: stable nat subtraction lowering *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module NatSubUnderflowSafe.
Definition sub_checked (a b : nat) : nat := a - b.
Definition sub_alt (a b : nat) : nat := b - a.
Definition t : nat := sub_checked 7 9 + sub_alt 9 7.
End NatSubUnderflowSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nat_sub_underflow_safe" NatSubUnderflowSafe.