(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidates for decode_list: empty, odd tail, pair count, single pair. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DecodeList.

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

Definition t_empty : nat := length (decode_list []).

Definition t_odd_tail : nat :=
  match decode_list [0; 99; 42] with
  | [NOP] => 1
  | _ => 0
  end.

Definition t_pair_count : nat := length (decode_list [0; 1; 2; 3]).

Definition t_single_pair : nat := length (decode_list [0; 7]).

End DecodeList.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_list" DecodeList.
