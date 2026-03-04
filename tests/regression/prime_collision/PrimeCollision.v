(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Repro: prime/underscore identifier escaping collision. *)

From Stdlib Require Import Nat.

Module PrimeCollision.

Definition foo' (n : nat) : nat := n.
Definition foo_ (n : nat) : nat := S n.

Definition t : nat := foo' 0 + foo_ 0.

End PrimeCollision.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prime_collision" PrimeCollision.
