(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: empty program has zero total cycle cost. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module ProgramCyclesEmpty.

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

Definition t : nat := program_cycles (mkState 0) [].

End ProgramCyclesEmpty.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "program_cycles_empty" ProgramCyclesEmpty.
