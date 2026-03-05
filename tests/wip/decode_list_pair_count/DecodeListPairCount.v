(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: decode_list yields one instruction per byte pair. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DecodeListPairCount.

Inductive instruction : Type :=
| NOP : instruction
| LDM : nat -> instruction.

Definition decode (b1 : nat) (b2 : nat) : instruction :=
  if b1 =? 0 then NOP else LDM (b2 mod 16).

Fixpoint decode_list (bytes : list nat) : list instruction :=
  match bytes with
  | [] => []
  | b1 :: b2 :: rest => decode b1 b2 :: decode_list rest
  | _ => []
  end.

Definition t : nat := length (decode_list [0; 1; 2; 3]).

End DecodeListPairCount.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_list_pair_count" DecodeListPairCount.
