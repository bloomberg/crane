(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral: program cycle count for singleton and multi-instruction programs. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module ProgramCycles.

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

(* Singleton program cycle count equals instruction cost (8) *)
Definition singleton_cycles : nat := program_cycles (mkState 0) [NOP].

(* Three NOPs contribute 24 total cycles *)
Definition three_nop_cycles : nat := program_cycles (mkState 0) [NOP; NOP; NOP].

Definition t : nat * nat := (singleton_cycles, three_nop_cycles).

End ProgramCycles.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "program_cycles" ProgramCycles.
