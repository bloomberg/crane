(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: page_base aligns addresses to 256-byte boundaries. *)

From Stdlib Require Import Nat.

Module DecodeWfOpcode2Behavior0072.

Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.

Definition t : nat := page_base 778 mod 272.

End DecodeWfOpcode2Behavior0072.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_wf_opcode_2_behavior_0072" DecodeWfOpcode2Behavior0072.
