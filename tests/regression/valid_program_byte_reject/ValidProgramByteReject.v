(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: valid_program rejects byte values outside the 0..255 range. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ValidProgramByteReject.

Definition valid_program (bytes : list nat) : bool :=
  (length bytes mod 2 =? 0) && forallb (fun b => b <? 256) bytes.

Definition t : bool := valid_program [0; 256].

End ValidProgramByteReject.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "valid_program_byte_reject" ValidProgramByteReject.
