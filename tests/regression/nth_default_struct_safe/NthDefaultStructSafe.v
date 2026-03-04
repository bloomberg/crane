(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: nth/default helpers generate consistent struct names *)

From Stdlib Require Import Bool.
From Stdlib Require Import Nat.

Module NthDefaultStructSafe.
Module L. Module SlotLeft. Definition nth0 (n : nat) : nat := n. End SlotLeft. End L.
Module R. Module SlotRight. Definition nth1 (n : nat) : nat := S n. End SlotRight. End R.
Definition t : nat := L.SlotLeft.nth0 1 + R.SlotRight.nth1 2.
End NthDefaultStructSafe.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nth_default_struct_safe" NthDefaultStructSafe.