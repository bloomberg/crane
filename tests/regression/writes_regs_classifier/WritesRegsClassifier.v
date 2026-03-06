(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: register-write instruction classifier. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WritesRegsClassifier.

Inductive instruction : Type :=
| XCH : nat -> instruction
| INC : nat -> instruction
| FIM : nat -> nat -> instruction
| FIN : nat -> instruction
| ISZ : nat -> nat -> instruction
| NOP : instruction
| ADD : nat -> instruction.

Definition writes_regs (i : instruction) : bool :=
  match i with
  | XCH _ | INC _ | FIM _ _ | FIN _ | ISZ _ _ => true
  | _ => false
  end.

Fixpoint count_writes_regs (prog : list instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if writes_regs i then 1 else 0) + count_writes_regs rest
  end.

Definition t : nat :=
  count_writes_regs [NOP; FIM 0 12; ADD 1; INC 7; ISZ 1 2].

End WritesRegsClassifier.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "writes_regs_classifier" WritesRegsClassifier.
