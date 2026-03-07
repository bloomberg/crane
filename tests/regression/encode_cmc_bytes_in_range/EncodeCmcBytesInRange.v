(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: CMC encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeCmcBytesInRange.

Inductive instruction : Type :=
| CMC : instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | CMC => (243, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode CMC).

End EncodeCmcBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_cmc_bytes_in_range" EncodeCmcBytesInRange.
