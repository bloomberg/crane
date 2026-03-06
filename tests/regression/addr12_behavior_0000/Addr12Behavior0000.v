(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: page_base aligns addresses to 256-byte boundaries. *)

From Stdlib Require Import Nat.

Module Addr12Behavior0000.

Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.

Definition t : nat := page_base 794 mod 271.

End Addr12Behavior0000.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "addr12_behavior_0000" Addr12Behavior0000.
