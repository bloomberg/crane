(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: per-instruction cycle accounting. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module InstructionCycleSum.

Record state : Type := MkState {
  acc_ : nat;
  carry_ : bool;
  test_ : bool
}.

Inductive instruction : Type :=
| NOP_
| JCN' : nat -> instruction
| INC_ : nat -> instruction.

Definition cycles (s : state) (i : instruction) : nat :=
  match i with
  | NOP_ => 8
  | JCN' n =>
      if Nat.eqb (n / 8) 1
      then 16
      else if andb (Nat.eqb (acc_ s) 0) (Nat.eqb ((n / 4) mod 2) 1) then 16 else 8
  | INC_ _ => 8
  end.

Definition execute (s : state) (i : instruction) : state :=
  match i with
  | NOP_ => s
  | JCN' _ => s
  | INC_ _ => MkState ((acc_ s + 1) mod 16) (carry_ s) (test_ s)
  end.

Fixpoint program_cycles (s : state) (prog : list instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => cycles s i + program_cycles (execute s i) rest
  end.

Definition t : nat := program_cycles (MkState 0 false true) [JCN' 8; INC_ 0; NOP_].

End InstructionCycleSum.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "instruction_cycle_sum" InstructionCycleSum.
