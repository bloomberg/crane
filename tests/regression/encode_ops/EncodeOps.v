(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined test: encoding operations for instruction encoding. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module EncodeOps.

(* === Instruction types from encode_bytes_in_range === *)

Inductive instruction1 : Type :=
| CLB : instruction1
| CMC : instruction1
| DAA : instruction1
| FIM : nat -> nat -> instruction1
| JUN : nat -> instruction1
| LDM1 : nat -> instruction1
| NOP1 : instruction1
| RDM : instruction1
| TCS : instruction1
| WPM : instruction1
| WR0 : instruction1.

Definition encode1 (i : instruction1) : nat * nat :=
  match i with
  | CLB => (240, 0)
  | CMC => (243, 0)
  | DAA => (251, 0)
  | FIM r d => (32 + (r - r mod 2), d mod 256)
  | JUN a => (64 + a / 256, a mod 256)
  | LDM1 n => (208 + n mod 16, 0)
  | NOP1 => (0, 0)
  | RDM => (233, 0)
  | TCS => (249, 0)
  | WPM => (227, 0)
  | WR0 => (228, 0)
  end.

Definition pair_in_range (p : nat * nat) : bool :=
  let '(b1, b2) := p in (b1 <? 256) && (b2 <? 256).

Definition test_encode_bytes_in_range : bool :=
  pair_in_range (encode1 CLB) &&
  pair_in_range (encode1 CMC) &&
  pair_in_range (encode1 DAA) &&
  pair_in_range (encode1 (FIM 14 255)) &&
  pair_in_range (encode1 (JUN 4095)) &&
  pair_in_range (encode1 (LDM1 15)) &&
  pair_in_range (encode1 NOP1) &&
  pair_in_range (encode1 RDM) &&
  pair_in_range (encode1 TCS) &&
  pair_in_range (encode1 WPM) &&
  pair_in_range (encode1 WR0).

(* === Instruction types from encode_list_byte_count === *)

Inductive instruction2 : Type :=
| NOP2 : instruction2
| LDM2 : nat -> instruction2.

Definition encode2 (i : instruction2) : nat * nat :=
  match i with
  | NOP2 => (0, 0)
  | LDM2 n => (13, n mod 16)
  end.

Fixpoint encode_list2 (prog : list instruction2) : list nat :=
  match prog with
  | [] => []
  | i :: rest =>
      let '(b1, b2) := encode2 i in
      b1 :: b2 :: encode_list2 rest
  end.

Definition test_encode_list_byte_count : nat :=
  length (encode_list2 [NOP2; LDM2 5; NOP2]).

(* === Instruction types from instruction_byte_stream_encode === *)

Inductive instruction3 : Type :=
| NOP3
| LDM3 : nat -> instruction3.

Definition encode3 (i : instruction3) : nat * nat :=
  match i with
  | NOP3 => (0, 0)
  | LDM3 n => (13 * 16 + (n mod 16), 0)
  end.

Fixpoint encode_list3 (prog : list instruction3) : list nat :=
  match prog with
  | [] => []
  | i :: rest =>
      let p := encode3 i in
      fst p :: snd p :: encode_list3 rest
  end.

Definition test_instruction_byte_stream_encode : nat :=
  length (encode_list3 [NOP3; LDM3 3; LDM3 12]).

(* Combined test tuple *)
Definition t : bool * nat * nat :=
  (test_encode_bytes_in_range,
   test_encode_list_byte_count,
   test_instruction_byte_stream_encode).

End EncodeOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_ops" EncodeOps.
