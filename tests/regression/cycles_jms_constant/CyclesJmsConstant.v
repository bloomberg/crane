(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JMS instruction has fixed 24-cycle cost. *)

From Stdlib Require Import Nat.

Module CyclesJmsConstant.

Inductive instruction : Type :=
| JMS : nat -> instruction
| NOP : instruction.

Record state : Type := mkState {
  acc : nat
}.

Definition cycles (_s : state) (i : instruction) : nat :=
  match i with
  | NOP => 8
  | JMS _ => 24
  end.

Definition t : nat := cycles (mkState 0) (JMS 77).

End CyclesJmsConstant.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "cycles_jms_constant" CyclesJmsConstant.
