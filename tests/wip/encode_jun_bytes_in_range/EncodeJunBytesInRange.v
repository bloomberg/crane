(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JUN encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeJunBytesInRange.

Inductive instruction : Type :=
| JUN : nat -> instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | JUN a => (64 + a / 256, a mod 256)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode (JUN 4095)).

End EncodeJunBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_jun_bytes_in_range" EncodeJunBytesInRange.
