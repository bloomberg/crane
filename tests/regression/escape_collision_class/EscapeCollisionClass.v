(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: escaped global identifier collision (keyword + suffixed variant). *)

From Stdlib Require Import Nat.

Module EscapeCollisionClass.

Definition class (n : nat) : nat := n.
Definition class_ (n : nat) : nat := S n.
Definition t : nat := class 1 + class_ 2.

End EscapeCollisionClass.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "escape_collision_class" EscapeCollisionClass.
