(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: jump_target filtering from instruction stream. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module JumpTargetCollection.

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

Fixpoint collect_targets (prog : list instruction) : list nat :=
  match prog with
  | [] => []
  | i :: rest =>
      match jump_target i with
      | Some a => a :: collect_targets rest
      | None => collect_targets rest
      end
  end.

Definition t : nat := length (collect_targets [JUN 17; NOP; JMS 511; NOP]).

End JumpTargetCollection.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_target_collection" JumpTargetCollection.
