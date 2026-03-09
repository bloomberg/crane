(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged test: instruction cycle behaviors *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module InstructionCycles.

(* ===== From cycles_jcn_not_taken ===== *)

Record state1 : Type := mkState1 {
  acc1 : nat;
  carry1 : bool;
  test_pin1 : bool
}.

Inductive instruction1 : Type :=
| JCN1 : nat -> nat -> instruction1
| NOP1 : instruction1.

Definition cycles_jcn (s : state1) (i : instruction1) : nat :=
  match i with
  | NOP1 => 8
  | JCN1 cond _ =>
      let c1 := cond / 8 in
      let c2 := (cond / 4) mod 2 in
      let c3 := (cond / 2) mod 2 in
      let c4 := cond mod 2 in
      let base_cond := orb (andb (acc1 s =? 0) (c2 =? 1))
                           (orb (andb (carry1 s) (c3 =? 1))
                                (andb (negb (test_pin1 s)) (c4 =? 1))) in
      let jump := if c1 =? 1 then negb base_cond else base_cond in
      if jump then 16 else 8
  end.

Definition test_cycles_jcn_not_taken : nat :=
  cycles_jcn (mkState1 1 false true) (JCN1 4 7).

(* ===== From cycles_jms_constant ===== *)

Inductive instruction2 : Type :=
| JMS2 : nat -> instruction2
| NOP2 : instruction2.

Record state2 : Type := mkState2 {
  acc2 : nat
}.

Definition cycles_jms (_s : state2) (i : instruction2) : nat :=
  match i with
  | NOP2 => 8
  | JMS2 _ => 24
  end.

Definition test_cycles_jms_constant : nat :=
  cycles_jms (mkState2 0) (JMS2 77).

(* ===== From min_cycles_per_instruction ===== *)

Inductive instr3 : Type :=
| NOP3
| ADD3
| WRM3
| FIM3
| JMS3
| JCNTaken3
| JCNNotTaken3
| ISZTaken3
| ISZZero3.

Definition cycles_min (i : instr3) : nat :=
  match i with
  | NOP3 | ADD3 | WRM3 | JCNNotTaken3 | ISZZero3 => 8
  | FIM3 | JCNTaken3 | ISZTaken3 => 16
  | JMS3 => 24
  end.

Definition all_instrs3 : list instr3 :=
  [NOP3; ADD3; WRM3; FIM3; JMS3; JCNTaken3; JCNNotTaken3; ISZTaken3; ISZZero3].

Definition test_min_cycles_per_instruction : bool :=
  forallb (fun i => Nat.leb 8 (cycles_min i)) all_instrs3.

(* ===== From max_cycles_per_instruction ===== *)

Inductive instr4 : Type :=
| NOP4
| ADD4
| WRM4
| FIM4
| JMS4
| JCNTaken4
| JCNNotTaken4
| ISZTaken4
| ISZZero4.

Definition cycles_max (i : instr4) : nat :=
  match i with
  | NOP4 | ADD4 | WRM4 | JCNNotTaken4 | ISZZero4 => 8
  | FIM4 | JCNTaken4 | ISZTaken4 => 16
  | JMS4 => 24
  end.

Definition all_instrs4 : list instr4 :=
  [NOP4; ADD4; WRM4; FIM4; JMS4; JCNTaken4; JCNNotTaken4; ISZTaken4; ISZZero4].

Definition test_max_cycles_per_instruction : bool :=
  forallb (fun i => Nat.leb (cycles_max i) 24) all_instrs4.

(* ===== From instruction_cycle_sum ===== *)

Record state5 : Type := MkState5 {
  acc5 : nat;
  carry5 : bool;
  test5 : bool
}.

Inductive instruction5 : Type :=
| NOP5
| JCN5 : nat -> instruction5
| INC5 : nat -> instruction5.

Definition cycles_sum (s : state5) (i : instruction5) : nat :=
  match i with
  | NOP5 => 8
  | JCN5 n =>
      if Nat.eqb (n / 8) 1
      then 16
      else if andb (Nat.eqb (acc5 s) 0) (Nat.eqb ((n / 4) mod 2) 1) then 16 else 8
  | INC5 _ => 8
  end.

Definition execute5 (s : state5) (i : instruction5) : state5 :=
  match i with
  | NOP5 => s
  | JCN5 _ => s
  | INC5 _ => MkState5 ((acc5 s + 1) mod 16) (carry5 s) (test5 s)
  end.

Fixpoint program_cycles5 (s : state5) (prog : list instruction5) : nat :=
  match prog with
  | [] => 0
  | i :: rest => cycles_sum s i + program_cycles5 (execute5 s i) rest
  end.

Definition test_instruction_cycle_sum : nat :=
  program_cycles5 (MkState5 0 false true) [JCN5 8; INC5 0; NOP5].

(* ===== From program_cycles ===== *)

Inductive instruction6 : Type :=
| NOP6 : instruction6.

Record state6 : Type := mkState6 {
  acc6 : nat
}.

Definition cycles6 (_s : state6) (_i : instruction6) : nat := 8.

Fixpoint program_cycles6 (s : state6) (prog : list instruction6) : nat :=
  match prog with
  | [] => 0
  | i :: rest => cycles6 s i + program_cycles6 s rest
  end.

Definition singleton_cycles6 : nat := program_cycles6 (mkState6 0) [NOP6].
Definition three_nop_cycles6 : nat := program_cycles6 (mkState6 0) [NOP6; NOP6; NOP6].

Definition test_program_cycles : nat * nat :=
  (singleton_cycles6, three_nop_cycles6).

(* ===== From program_cycles_single ===== *)

Inductive instruction7 : Type :=
| NOP7 : instruction7.

Record state7 : Type := mkState7 {
  acc7 : nat
}.

Definition cycles7 (_s : state7) (_i : instruction7) : nat := 8.

Fixpoint program_cycles7 (s : state7) (prog : list instruction7) : nat :=
  match prog with
  | [] => 0
  | i :: rest => cycles7 s i + program_cycles7 s rest
  end.

Definition test_program_cycles_single : nat :=
  program_cycles7 (mkState7 16) [NOP7].

(* ===== Combined test value ===== *)

Definition t : nat * nat * bool * bool * nat * (nat * nat) * nat :=
  (test_cycles_jcn_not_taken,
   test_cycles_jms_constant,
   test_min_cycles_per_instruction,
   test_max_cycles_per_instruction,
   test_instruction_cycle_sum,
   test_program_cycles,
   test_program_cycles_single).

End InstructionCycles.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "instruction_cycles" InstructionCycles.
