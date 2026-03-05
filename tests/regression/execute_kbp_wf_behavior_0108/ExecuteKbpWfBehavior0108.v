(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: page_base aligns addresses to 256-byte boundaries. *)

From Stdlib Require Import Nat.

Module ExecuteKbpWfBehavior0108.

Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.

Definition t : nat := page_base 779 mod 269.

End ExecuteKbpWfBehavior0108.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "execute_kbp_wf_behavior_0108" ExecuteKbpWfBehavior0108.
