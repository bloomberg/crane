(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: FIM encodes to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeFimBytesInRange.

Inductive instruction : Type :=
| FIM : nat -> nat -> instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | FIM r d => (32 + (r - r mod 2), d mod 256)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool := pair_in_range (encode (FIM 14 255)).

End EncodeFimBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_fim_bytes_in_range" EncodeFimBytesInRange.
