(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Repro: escaped module-path leaf collision (prime vs underscore). *)

From Stdlib Require Import Nat.

Module ModpathEscapeCollision.

Module A.
  Module Token'.
    Definition f (n : nat) : nat := n.
  End Token'.
End A.

Module B.
  Module Token_.
    Definition g (n : nat) : nat := S n.
  End Token_.
End B.

Definition t : nat := A.Token'.f 0 + B.Token_.g 0.

End ModpathEscapeCollision.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "modpath_escape_collision" ModpathEscapeCollision.
