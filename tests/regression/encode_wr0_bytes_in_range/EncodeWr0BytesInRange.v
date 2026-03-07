(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: WR0 encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeWr0BytesInRange.

Inductive instruction : Type :=
| WR0 : instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | WR0 => (228, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode WR0).

End EncodeWr0BytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_wr0_bytes_in_range" EncodeWr0BytesInRange.
