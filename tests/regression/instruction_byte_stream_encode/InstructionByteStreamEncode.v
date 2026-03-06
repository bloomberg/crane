(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: encode_list flattening instruction bytes. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module InstructionByteStreamEncode.

Inductive instruction : Type :=
| NOP
| LDM : nat -> instruction.

Definition encode (i : instruction) : nat * nat :=
  match i with
  | NOP => (0, 0)
  | LDM n => (13 * 16 + (n mod 16), 0)
  end.

Fixpoint encode_list (prog : list instruction) : list nat :=
  match prog with
  | [] => []
  | i :: rest =>
      let p := encode i in
      fst p :: snd p :: encode_list rest
  end.

Definition t : nat := length (encode_list [NOP; LDM 3; LDM 12]).

End InstructionByteStreamEncode.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "instruction_byte_stream_encode" InstructionByteStreamEncode.
