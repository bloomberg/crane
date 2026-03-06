(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: verify all jump targets are inside program layout. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ProgramTargetsRegionScan.

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

Definition addr_in_regionb (addr : nat) (l : layout) : bool :=
  (base_addr l <=? addr) && (addr <? base_addr l + code_size l).

Definition target_in_layoutb (l : layout) (i : instruction) : bool :=
  match jump_target i with
  | Some a => addr_in_regionb a l
  | None => true
  end.

Definition program_targets_okb (prog : list instruction) (l : layout) : bool :=
  forallb (target_in_layoutb l) prog.

Definition t : nat :=
  let l := mkLayout 200 20 in
  let p := [NOP; JUN 205; JMS 218] in
  if program_targets_okb p l then 1 else 0.

End ProgramTargetsRegionScan.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "program_targets_region_scan" ProgramTargetsRegionScan.
