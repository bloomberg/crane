(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: program_wf remains Prop-valued over out-of-region jump targets. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module ProgramWfTargetsOutsideProp.

Inductive instruction : Type :=
| JUN : nat -> instruction
| JMS : nat -> instruction
| NOP : instruction.

Record layout : Type := mkLayout {
  base_addr : nat;
  code_size : nat
}.

Definition valid_layout (l : layout) : Prop :=
  base_addr l + code_size l <= 4096.

Definition addr_in_region (addr : nat) (l : layout) : Prop :=
  base_addr l <= addr < base_addr l + code_size l.

Definition jump_target (i : instruction) : option nat :=
  match i with
  | JUN a => Some a
  | JMS a => Some a
  | NOP => None
  end.

Definition program_wf (prog : list instruction) (l : layout) : Prop :=
  valid_layout l /\
  Forall (fun i =>
    match jump_target i with
    | Some addr => addr_in_region addr l
    | None => True
    end) prog.

Definition t : Prop := program_wf [JUN 205; JMS 400] (mkLayout 200 20).

End ProgramWfTargetsOutsideProp.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "program_wf_targets_outside_prop" ProgramWfTargetsOutsideProp.
