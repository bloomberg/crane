(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: JUN exposes its concrete jump target address. *)

From Stdlib Require Import Nat.

Module JumpTargetSomeJun.

Inductive instruction : Type :=
| JUN : nat -> instruction
| JMS : nat -> instruction
| NOP : instruction.

Definition jump_target (i : instruction) : option nat :=
  match i with
  | JUN a => Some a
  | JMS a => Some a
  | NOP => None
  end.

Definition target_default (o : option nat) : nat :=
  match o with
  | Some a => a
  | None => 0
  end.

Definition t : nat := target_default (jump_target (JUN 511)).

End JumpTargetSomeJun.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_target_some_jun" JumpTargetSomeJun.
