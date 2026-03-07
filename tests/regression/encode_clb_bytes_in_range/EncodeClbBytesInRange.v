(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: CLB encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeClbBytesInRange.

Inductive instruction : Type :=
| CLB : instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | CLB => (240, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode CLB).

End EncodeClbBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_clb_bytes_in_range" EncodeClbBytesInRange.
