(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: program WF/layout infrastructure. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module ProgramWf.

Inductive instruction : Type :=
| JUN : nat -> instruction
| JMS : nat -> instruction
| NOP : instruction.

Record layout : Type := mkLayout {
  base_addr : nat;
  code_size : nat
}.

Definition jump_target (i : instruction) : option nat :=
  match i with
  | JUN a => Some a
  | JMS a => Some a
  | NOP => None
  end.

Definition sample_layout : layout := mkLayout 200 20.
Definition sample_prog : list instruction := [NOP; JUN 205; JMS 218].

Definition sample_code_size : nat := code_size sample_layout.

End ProgramWf.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "program_wf" ProgramWf.
