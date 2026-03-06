(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: RAM-write instruction classifier. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WritesRamClassifier.

Inductive instruction : Type :=
| WRM : instruction
| WMP : instruction
| WR0 : instruction
| WR1 : instruction
| WR2 : instruction
| WR3 : instruction
| NOP : instruction
| ADD : nat -> instruction.

Definition writes_ram (i : instruction) : bool :=
  match i with
  | WRM | WMP | WR0 | WR1 | WR2 | WR3 => true
  | _ => false
  end.

Fixpoint count_writes_ram (prog : list instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if writes_ram i then 1 else 0) + count_writes_ram rest
  end.

Definition t : nat :=
  count_writes_ram [NOP; WRM; ADD 3; WR3; WMP; NOP].

End WritesRamClassifier.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "writes_ram_classifier" WritesRamClassifier.
