(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: prime-suffixed vs underscore-suffixed identifier collision. *)

From Stdlib Require Import Nat.

Module PrimeCollisionValue.

Definition value' (n : nat) : nat := n.
Definition value_ (n : nat) : nat := S n.
Definition t : nat := value' 0 + value_ 0.

End PrimeCollisionValue.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prime_collision_value" PrimeCollisionValue.
