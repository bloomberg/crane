(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: valid_program accepts even-length in-range byte streams. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module DecodeLdmWfBehavior0068.

Definition valid_program (bytes : list nat) : bool :=
  (length bytes mod 2 =? 0) && forallb (fun b => b <? 256) bytes.

Definition t : bool := valid_program [9; 260; 0; 42].

End DecodeLdmWfBehavior0068.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_ldm_wf_behavior_0068" DecodeLdmWfBehavior0068.
