(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: CPU instruction WF infrastructure. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module CpuInstrWf.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  ex_acc : nat;
  ex_regs : list nat;
  ex_carry : bool;
  ex_pc : nat;
  ex_stack : list nat;
  ex_pair_bus : nat;
  ex_ports : list nat
}.

Definition get_reg (s : state) (r : nat) : nat :=
  nth r (ex_regs s) 0.

Definition set_reg (s : state) (r v : nat) : list nat :=
  update_nth r (v mod 16) (ex_regs s).

Definition pair_base (r : nat) : nat :=
  r - r mod 2.

Definition get_pair (s : state) (r : nat) : nat :=
  let base := pair_base r in
  ((get_reg s base) mod 16) * 16 + (get_reg s (S base) mod 16).

Definition set_pair (s : state) (r v : nat) : list nat :=
  let base := pair_base r in
  let hi := (v / 16) mod 16 in
  let lo := v mod 16 in
  update_nth (S base) lo (update_nth base hi (ex_regs s)).

Definition push_return (s : state) (ret : nat) : list nat :=
  firstn 2 ((ret mod 4096) :: ex_stack s).

Inductive instr : Type :=
| NOP
| LDM (n : nat)
| LD (r : nat)
| XCH (r : nat)
| INC (r : nat)
| ADD (r : nat)
| SUB (r : nat)
| IAC
| DAC
| CLC
| STC
| CMC
| CMA
| CLB
| RAL
| RAR
| TCC
| TCS
| DAA
| KBP
| JUN (a : nat)
| JMS (a : nat)
| JCN (c : nat) (a : nat)
| FIM (r : nat) (d : nat)
| SRC (r : nat)
| FIN (r : nat)
| JIN (r : nat)
| ISZ (r : nat) (a : nat)
| BBL (d : nat).

Definition execute (s : state) (i : instr) : state :=
  match i with
  | NOP =>
      mkState (ex_acc s) (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | LDM n =>
      mkState (n mod 16) (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | LD r =>
      mkState (get_reg s r) (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | XCH r =>
      let regv := get_reg s r in
      mkState regv (set_reg s r (ex_acc s)) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | INC r =>
      mkState (ex_acc s) (set_reg s r (S (get_reg s r))) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | ADD r =>
      let sum := ex_acc s + get_reg s r + if ex_carry s then 1 else 0 in
      mkState (sum mod 16) (ex_regs s) (Nat.leb 16 sum) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | SUB r =>
      let diff := ex_acc s + 16 - get_reg s r in
      mkState (diff mod 16) (ex_regs s) (Nat.leb (get_reg s r) (ex_acc s)) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | IAC =>
      mkState ((S (ex_acc s)) mod 16) (ex_regs s) (Nat.leb 16 (S (ex_acc s))) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | DAC =>
      mkState ((ex_acc s + 15) mod 16) (ex_regs s) (negb (Nat.eqb (ex_acc s) 0)) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | CLC =>
      mkState (ex_acc s) (ex_regs s) false ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | STC =>
      mkState (ex_acc s) (ex_regs s) true ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | CMC =>
      mkState (ex_acc s) (ex_regs s) (negb (ex_carry s)) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | CMA =>
      mkState (15 - ex_acc s) (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | CLB =>
      mkState 0 (ex_regs s) false ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | RAL =>
      let acc' := ((2 * ex_acc s) + if ex_carry s then 1 else 0) mod 16 in
      let carry' := Nat.leb 16 ((2 * ex_acc s) + if ex_carry s then 1 else 0) in
      mkState acc' (ex_regs s) carry' ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | RAR =>
      let carry_bit := if ex_carry s then 8 else 0 in
      mkState ((ex_acc s / 2) + carry_bit) (ex_regs s) (Nat.eqb (ex_acc s mod 2) 1) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | TCC =>
      mkState (if ex_carry s then 1 else 0) (ex_regs s) false ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | TCS =>
      mkState (if ex_carry s then 10 else 9) (ex_regs s) false ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | DAA =>
      let acc' := if Nat.leb 10 (S (ex_acc s)) then (ex_acc s + 6) mod 16 else ex_acc s in
      mkState acc' (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | KBP =>
      let a := ex_acc s in
      let out :=
        if Nat.eqb a 0 then 0 else
        if Nat.eqb a 1 then 0 else
        if Nat.eqb a 2 then 1 else
        if Nat.eqb a 4 then 2 else
        if Nat.eqb a 8 then 3 else 15 in
      mkState out (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | JUN a =>
      mkState (ex_acc s) (ex_regs s) (ex_carry s) (a mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | JMS a =>
      mkState (ex_acc s) (ex_regs s) (ex_carry s) (a mod 4096)
              (push_return s (ex_pc s + 2)) (ex_pair_bus s) (ex_ports s)
  | JCN c a =>
      let jump := Nat.eqb (c mod 2) 1 && ex_carry s in
      mkState (ex_acc s) (ex_regs s) (ex_carry s)
              (if jump then a mod 4096 else (ex_pc s + 2) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | FIM r d =>
      mkState (ex_acc s) (set_pair s r d) (ex_carry s) ((ex_pc s + 2) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | SRC r =>
      mkState (ex_acc s) (ex_regs s) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (get_pair s r) (ex_ports s)
  | FIN r =>
      mkState (ex_acc s) (set_pair s r (ex_pair_bus s)) (ex_carry s) ((ex_pc s + 1) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | JIN r =>
      mkState (ex_acc s) (ex_regs s) (ex_carry s) (get_pair s r mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | ISZ r a =>
      let n := (S (get_reg s r)) mod 16 in
      mkState (ex_acc s) (set_reg s r n) (ex_carry s)
              (if Nat.eqb n 0 then a mod 4096 else (ex_pc s + 2) mod 4096)
              (ex_stack s) (ex_pair_bus s) (ex_ports s)
  | BBL d =>
      mkState (d mod 16) (ex_regs s) (ex_carry s) (nth 0 (ex_stack s) 0)
              (skipn 1 (ex_stack s)) (ex_pair_bus s) (ex_ports s)
  end.

Definition sample : state :=
  mkState 3 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 0]
          false 10 [20; 30] 42 [1; 2; 3; 4].

Definition nop_acc : nat := ex_acc (execute sample NOP).

End CpuInstrWf.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "cpu_instr_wf" CpuInstrWf.
