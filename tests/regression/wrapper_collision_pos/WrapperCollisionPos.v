(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 1: wrapper name collision when distinct modules share basename Pos. *)

From Stdlib Require Import Nat.

Module WrapperCollisionPos.

Module Left.
  Module Pos.
    Definition id_left (n : nat) : nat := n.
  End Pos.
End Left.

Module Right.
  Module Pos.
    Definition inc_right (n : nat) : nat := S n.
  End Pos.
End Right.

Definition t1 : nat := Left.Pos.id_left 1.
Definition t2 : nat := Right.Pos.inc_right 1.

End WrapperCollisionPos.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wrapper_collision_pos" WrapperCollisionPos.