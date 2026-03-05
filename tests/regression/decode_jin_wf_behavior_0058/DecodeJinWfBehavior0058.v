(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: ISZ terminates when register value wraps from 15. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module DecodeJinWfBehavior0058.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition nibble_of_nat (n : nat) : nat := n mod 16.

Definition isz_terminates (s : state) (r : nat) : bool :=
  nibble_of_nat (get_reg s r + 1) =? 0.

Definition t : bool := isz_terminates (mkState [30]) 2.

End DecodeJinWfBehavior0058.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_jin_wf_behavior_0058" DecodeJinWfBehavior0058.
