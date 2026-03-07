(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: NOP encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeNopBytesInRange.

Inductive instruction : Type :=
| NOP : instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | NOP => (0, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode NOP).

End EncodeNopBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_nop_bytes_in_range" EncodeNopBytesInRange.
