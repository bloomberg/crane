(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Repro: escaped global identifier collision (keyword + suffixed variant). *)

From Stdlib Require Import Nat.

Module EscapeCollision.

Definition double (n : nat) : nat := n.
Definition double_ (n : nat) : nat := S n.

Definition t : nat := double 1 + double_ 2.

End EscapeCollision.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "escape_collision" EscapeCollision.
