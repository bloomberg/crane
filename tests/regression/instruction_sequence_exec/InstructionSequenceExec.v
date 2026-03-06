(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: exec_program sequencing over instruction list. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module InstructionSequenceExec.

Record state : Type := MkState {
  pc_ : nat;
  acc_ : nat
}.

Inductive instruction : Type :=
| NOP_
| INC_PC
| ADD_ACC : nat -> instruction.

Definition execute (s : state) (i : instruction) : state :=
  match i with
  | NOP_ => s
  | INC_PC => MkState (S (pc_ s)) (acc_ s)
  | ADD_ACC n => MkState (pc_ s) (acc_ s + n)
  end.

Fixpoint exec_program (prog : list instruction) (s : state) : state :=
  match prog with
  | [] => s
  | i :: rest => exec_program rest (execute s i)
  end.

Definition sample : state := MkState 0 1.
Definition t : nat :=
  let s' := exec_program [INC_PC; ADD_ACC 2; INC_PC] sample in
  pc_ s' + acc_ s'.

End InstructionSequenceExec.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "instruction_sequence_exec" InstructionSequenceExec.
