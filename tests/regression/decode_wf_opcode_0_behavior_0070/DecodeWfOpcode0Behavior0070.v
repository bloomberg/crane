(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: valid_program rejects odd-length byte streams. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module DecodeWfOpcode0Behavior0070.

Definition valid_program (bytes : list nat) : bool :=
  (length bytes mod 2 =? 0) && forallb (fun b => b <? 256) bytes.

Definition t : bool := valid_program [18; 8; 3].

End DecodeWfOpcode0Behavior0070.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_wf_opcode_0_behavior_0070" DecodeWfOpcode0Behavior0070.
