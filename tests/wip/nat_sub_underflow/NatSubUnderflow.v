(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: nat subtraction helpers under prime/underscore naming *)

From Stdlib Require Import Nat.

Module NatSubUnderflow.

Definition value' (n : nat) : nat := n.
Definition value_ (n : nat) : nat := S n.
Definition t : nat := value' 1 + value_ 2.
End NatSubUnderflow.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nat_sub_underflow" NatSubUnderflow.