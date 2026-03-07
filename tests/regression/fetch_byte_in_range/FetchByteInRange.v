(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: fetch_byte reads bytes in range directly from ROM. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module FetchByteInRange.

Definition fetch_byte (rom : list nat) (addr : nat) : nat := nth addr rom 0.

Definition t : nat := fetch_byte [11; 22; 33] 1.

End FetchByteInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "fetch_byte_in_range" FetchByteInRange.
