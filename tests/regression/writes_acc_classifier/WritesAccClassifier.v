(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: accumulator-write instruction classifier. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WritesAccClassifier.

Inductive instruction : Type :=
| LDM : nat -> instruction
| LD : nat -> instruction
| ADD : nat -> instruction
| SUB : nat -> instruction
| INC : nat -> instruction
| XCH : nat -> instruction
| BBL : nat -> instruction
| SBM : instruction
| RDM : instruction
| RDR : instruction
| ADM : instruction
| RD0 : instruction
| RD1 : instruction
| RD2 : instruction
| RD3 : instruction
| CLB : instruction
| CMA : instruction
| IAC : instruction
| DAC : instruction
| RAL : instruction
| RAR : instruction
| TCC : instruction
| TCS : instruction
| DAA : instruction
| KBP : instruction
| NOP : instruction.

Definition writes_acc (i : instruction) : bool :=
  match i with
  | LDM _ | LD _ | ADD _ | SUB _ | INC _ | XCH _ | BBL _
  | SBM | RDM | RDR | ADM | RD0 | RD1 | RD2 | RD3
  | CLB | CMA | IAC | DAC | RAL | RAR | TCC | TCS | DAA | KBP => true
  | _ => false
  end.

Fixpoint count_writes_acc (prog : list instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if writes_acc i then 1 else 0) + count_writes_acc rest
  end.

Definition t : nat :=
  count_writes_acc [NOP; LDM 9; RAR; KBP; NOP; ADD 1].

End WritesAccClassifier.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "writes_acc_classifier" WritesAccClassifier.
