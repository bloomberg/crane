(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: recombine page base and page offset. *)

From Stdlib Require Import Nat.

Module DecodeWfOpcode15Edge0085.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.
Definition page_offset (p : nat) : nat := p mod 256.

Definition recompose (p : nat) : nat := page_base p + page_offset p.

Definition t : nat := recompose (addr12_of_nat 1027).

End DecodeWfOpcode15Edge0085.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_wf_opcode_15_edge_0085" DecodeWfOpcode15Edge0085.
