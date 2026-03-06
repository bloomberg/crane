(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: two NOPs contribute 16 total cycles. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DecodeOpcode3WfBehavior0046.

Inductive instruction : Type :=
| NOP : instruction.

Record state : Type := mkState {
  acc : nat
}.

Definition cycles (_s : state) (_i : instruction) : nat := 8.

Fixpoint program_cycles (s : state) (prog : list instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => cycles s i + program_cycles s rest
  end.

Definition t : nat := program_cycles (mkState 17) [NOP; NOP].

End DecodeOpcode3WfBehavior0046.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "decode_opcode_3_wf_behavior_0046" DecodeOpcode3WfBehavior0046.
