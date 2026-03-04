(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: match-forward shape under shadow-qualified names *)

From Stdlib Require Import Bool.

Module MatchForwardOrder.

Module Node.
  Inductive shadow : Type := TagA | TagB.
End Node.

Definition pick (b : bool) : Node.shadow := if b then Node.TagA else Node.TagB.
Definition t : Node.shadow := pick true.
End MatchForwardOrder.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "match_forward_order" MatchForwardOrder.