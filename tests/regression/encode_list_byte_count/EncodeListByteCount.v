(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: encode_list emits two bytes per instruction. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module EncodeListByteCount.

Inductive instruction : Type :=
| NOP : instruction
| LDM : nat -> instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | NOP => (0, 0)
  | LDM n => (13, n mod 16)
  end.

Fixpoint encode_list (prog : list instruction) : list nat :=
  match prog with
  | [] => []
  | i :: rest =>
      let '(b1, b2) := encode i in
      b1 :: b2 :: encode_list rest
  end.

Definition t : nat := length (encode_list [NOP; LDM 5; NOP]).

End EncodeListByteCount.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "encode_list_byte_count" EncodeListByteCount.
