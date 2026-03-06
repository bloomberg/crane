(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: classify branch-like opcodes from instruction stream. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module JumpClassifierFlags.

Inductive instruction : Type :=
| JCN : nat -> nat -> instruction
| JUN : nat -> instruction
| JMS : nat -> instruction
| JIN : nat -> instruction
| BBL : nat -> instruction
| ISZ : nat -> nat -> instruction
| ADD : nat -> instruction
| NOP : instruction.

Definition is_jump (i : instruction) : bool :=
  match i with
  | JCN _ _ | JUN _ | JMS _ | JIN _ | BBL _ | ISZ _ _ => true
  | _ => false
  end.

Fixpoint count_jumps (prog : list instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if is_jump i then 1 else 0) + count_jumps rest
  end.

Definition t : nat :=
  count_jumps [ADD 0; JCN 4 8; NOP; JMS 33; ISZ 1 2].

End JumpClassifierFlags.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_classifier_flags" JumpClassifierFlags.
