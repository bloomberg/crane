(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: All instructions encode to byte-range values. *)

From Stdlib Require Import Nat Bool.

Module EncodeBytesInRange.

Inductive instruction : Type :=
| CLB : instruction
| CMC : instruction
| DAA : instruction
| FIM : nat -> nat -> instruction
| JUN : nat -> instruction
| LDM : nat -> instruction
| NOP : instruction
| RDM : instruction
| TCS : instruction
| WPM : instruction
| WR0 : instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | CLB => (240, 0)
  | CMC => (243, 0)
  | DAA => (251, 0)
  | FIM r d => (32 + (r - r mod 2), d mod 256)
  | JUN a => (64 + a / 256, a mod 256)
  | LDM n => (208 + n mod 16, 0)
  | NOP => (0, 0)
  | RDM => (233, 0)
  | TCS => (249, 0)
  | WPM => (227, 0)
  | WR0 => (228, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition t : bool :=
  pair_in_range (encode CLB) &&
  pair_in_range (encode CMC) &&
  pair_in_range (encode DAA) &&
  pair_in_range (encode (FIM 14 255)) &&
  pair_in_range (encode (JUN 4095)) &&
  pair_in_range (encode (LDM 15)) &&
  pair_in_range (encode NOP) &&
  pair_in_range (encode RDM) &&
  pair_in_range (encode TCS) &&
  pair_in_range (encode WPM) &&
  pair_in_range (encode WR0).

End EncodeBytesInRange.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_bytes_in_range" EncodeBytesInRange.
