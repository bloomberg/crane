(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: wrapper naming remains unique when basename is Token. *)

From Stdlib Require Import Nat.

Module WrapperCollisionToken.

Module Left.
  Module Token.
    Definition id_left (n : nat) : nat := n.
  End Token.
End Left.

Module Right.
  Module Token.
    Definition inc_right (n : nat) : nat := S n.
  End Token.
End Right.

Definition t1 : nat := Left.Token.id_left 2.
Definition t2 : nat := Right.Token.inc_right 2.

End WrapperCollisionToken.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wrapper_collision_token" WrapperCollisionToken.
