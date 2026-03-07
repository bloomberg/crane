(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: jump_target exposes JMS destination addresses. *)

From Stdlib Require Import Nat.

Module JumpTargetSomeJms.

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

Definition option_nat_or_zero (o : option nat) : nat :=
  match o with
  | Some n => n
  | None => 0
  end.

Definition t : nat := option_nat_or_zero (jump_target (JMS 144)).

End JumpTargetSomeJms.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_target_some_jms" JumpTargetSomeJms.
