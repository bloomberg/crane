(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: program validity check for even length and byte bounds. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ValidProgramChecks.

Definition valid_program (bytes : list nat) : bool :=
  (length bytes mod 2 =? 0) && forallb (fun b => b <? 256) bytes.

Definition t : nat :=
  (if valid_program [1; 2; 3; 4] then 1 else 0) +
  (if valid_program [1; 2; 300] then 1 else 0).

End ValidProgramChecks.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "valid_program_checks" ValidProgramChecks.
