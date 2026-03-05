(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: valid_program accepts even-length in-range byte streams. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ExecuteRarWfBehavior0104.

Definition valid_program (bytes : list nat) : bool :=
  (length bytes mod 2 =? 0) && forallb (fun b => b <? 256) bytes.

Definition t : bool := valid_program [14; 271; 0; 42].

End ExecuteRarWfBehavior0104.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "execute_rar_wf_behavior_0104" ExecuteRarWfBehavior0104.
