(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: qualified-name shadowing inside nested module scope. *)

From Stdlib Require Import Nat.

Module ShadowQualNode.

Module Node.
  Inductive shadow : Type := Tag.
End Node.

Definition id (x : Node.shadow) : Node.shadow := x.
Definition t : Node.shadow := id Node.Tag.

End ShadowQualNode.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "shadow_qual_node" ShadowQualNode.
