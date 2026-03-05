(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: non-jump instruction has no jump target. *)

From Stdlib Require Import Nat Bool.

Module JumpTargetNoneDefault.

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

Definition is_none {A : Type} (o : option A) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition t : bool := is_none (jump_target NOP).

End JumpTargetNoneDefault.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_target_none_default" JumpTargetNoneDefault.
