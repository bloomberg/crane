(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged instruction classifier tests: accumulator, RAM, registers, and jump classifiers. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module InstructionClassifiers.

(* Accumulator-write instruction classifier *)
Inductive instr_acc : Type :=
| LDM : nat -> instr_acc
| LD : nat -> instr_acc
| ADD : nat -> instr_acc
| SUB : nat -> instr_acc
| INC : nat -> instr_acc
| XCH : nat -> instr_acc
| BBL : nat -> instr_acc
| SBM : instr_acc
| RDM : instr_acc
| RDR : instr_acc
| ADM : instr_acc
| RD0 : instr_acc
| RD1 : instr_acc
| RD2 : instr_acc
| RD3 : instr_acc
| CLB : instr_acc
| CMA : instr_acc
| IAC : instr_acc
| DAC : instr_acc
| RAL : instr_acc
| RAR : instr_acc
| TCC : instr_acc
| TCS : instr_acc
| DAA : instr_acc
| KBP : instr_acc
| NOP_acc : instr_acc.

Definition writes_acc (i : instr_acc) : bool :=
  match i with
  | LDM _ | LD _ | ADD _ | SUB _ | INC _ | XCH _ | BBL _
  | SBM | RDM | RDR | ADM | RD0 | RD1 | RD2 | RD3
  | CLB | CMA | IAC | DAC | RAL | RAR | TCC | TCS | DAA | KBP => true
  | _ => false
  end.

Fixpoint count_writes_acc (prog : list instr_acc) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if writes_acc i then 1 else 0) + count_writes_acc rest
  end.

Definition test_writes_acc : nat :=
  count_writes_acc [NOP_acc; LDM 9; RAR; KBP; NOP_acc; ADD 1].

(* RAM-write instruction classifier *)
Inductive instr_ram : Type :=
| WRM : instr_ram
| WMP : instr_ram
| WR0 : instr_ram
| WR1 : instr_ram
| WR2 : instr_ram
| WR3 : instr_ram
| NOP_ram : instr_ram
| ADD_ram : nat -> instr_ram.

Definition writes_ram (i : instr_ram) : bool :=
  match i with
  | WRM | WMP | WR0 | WR1 | WR2 | WR3 => true
  | _ => false
  end.

Fixpoint count_writes_ram (prog : list instr_ram) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if writes_ram i then 1 else 0) + count_writes_ram rest
  end.

Definition test_writes_ram : nat :=
  count_writes_ram [NOP_ram; WRM; ADD_ram 3; WR3; WMP; NOP_ram].

(* Register-write instruction classifier *)
Inductive instr_regs : Type :=
| XCH_regs : nat -> instr_regs
| INC_regs : nat -> instr_regs
| FIM : nat -> nat -> instr_regs
| FIN : nat -> instr_regs
| ISZ : nat -> nat -> instr_regs
| NOP_regs : instr_regs
| ADD_regs : nat -> instr_regs.

Definition writes_regs (i : instr_regs) : bool :=
  match i with
  | XCH_regs _ | INC_regs _ | FIM _ _ | FIN _ | ISZ _ _ => true
  | _ => false
  end.

Fixpoint count_writes_regs (prog : list instr_regs) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if writes_regs i then 1 else 0) + count_writes_regs rest
  end.

Definition test_writes_regs : nat :=
  count_writes_regs [NOP_regs; FIM 0 12; ADD_regs 1; INC_regs 7; ISZ 1 2].

(* Jump instruction classifier *)
Inductive instr_jump : Type :=
| JCN : nat -> nat -> instr_jump
| JUN : nat -> instr_jump
| JMS : nat -> instr_jump
| JIN : nat -> instr_jump
| BBL_jump : nat -> instr_jump
| ISZ_jump : nat -> nat -> instr_jump
| ADD_jump : nat -> instr_jump
| NOP_jump : instr_jump.

Definition is_jump (i : instr_jump) : bool :=
  match i with
  | JCN _ _ | JUN _ | JMS _ | JIN _ | BBL_jump _ | ISZ_jump _ _ => true
  | _ => false
  end.

Fixpoint count_jumps (prog : list instr_jump) : nat :=
  match prog with
  | [] => 0
  | i :: rest => (if is_jump i then 1 else 0) + count_jumps rest
  end.

Definition test_jump_classifier : nat :=
  count_jumps [ADD_jump 0; JCN 4 8; NOP_jump; JMS 33; ISZ_jump 1 2].

(* Combined test result as tuple *)
Definition t : nat * nat * nat * nat :=
  (test_writes_acc, test_writes_ram, test_writes_regs, test_jump_classifier).

End InstructionClassifiers.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "instruction_classifiers" InstructionClassifiers.
