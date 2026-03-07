(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: WPM encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeWpmBytesInRange.

Inductive instruction : Type :=
| WPM : instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | WPM => (227, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode WPM).

End EncodeWpmBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_wpm_bytes_in_range" EncodeWpmBytesInRange.
