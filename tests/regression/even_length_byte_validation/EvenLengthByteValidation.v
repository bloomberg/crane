(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: valid_program byte stream checks. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module EvenLengthByteValidation.

Definition valid_program (bytes : list nat) : bool :=
  (Nat.eqb (length bytes mod 2) 0) && forallb (fun b => b <? 256) bytes.

Definition t : nat := if valid_program [1; 2; 3; 4] then 1 else 0.

End EvenLengthByteValidation.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "even_length_byte_validation" EvenLengthByteValidation.
