(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: RAM bad state construction. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamBadState.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record ram_reg : Type := mkReg {
  reg_main : list nat;
  reg_status : list nat
}.

Record ram_chip : Type := mkChip {
  chip_regs : list ram_reg;
  chip_port : nat
}.

Record ram_bank : Type := mkBank {
  bank_chips : list ram_chip
}.

Record ram_sel : Type := mkSel {
  sel_bank : nat;
  sel_chip : nat;
  sel_reg : nat;
  sel_char : nat
}.

Record state : Type := mkState {
  state_regs : list nat;
  state_acc : nat;
  state_carry : bool;
  state_pc : nat;
  state_stack : list nat;
  state_ram : list ram_bank;
  state_sel : ram_sel;
  state_rom : list nat
}.

Definition empty_reg : ram_reg := mkReg (repeat 0 16) (repeat 0 4).
Definition empty_chip : ram_chip := mkChip (repeat empty_reg 4) 0.
Definition empty_bank : ram_bank := mkBank (repeat empty_chip 4).
Definition empty_ram : list ram_bank := repeat empty_bank 4.
Definition default_sel : ram_sel := mkSel 0 0 0 0.

Definition bad_state_acc_overflow : state :=
  mkState (repeat 0 16) 16 false 0 [] empty_ram default_sel (repeat 0 8).

Definition bad_state_pc_overflow : state :=
  mkState (repeat 0 16) 0 false 4096 [] empty_ram default_sel (repeat 0 8).

Definition bad_state_stack_overflow : state :=
  mkState (repeat 0 16) 0 false 0 [0; 1; 2; 3] empty_ram default_sel (repeat 0 8).

Definition bad_state_wrong_reg_count : state :=
  mkState (repeat 0 15) 0 false 0 [] empty_ram default_sel (repeat 0 8).

Definition overflow_acc : nat := state_acc bad_state_acc_overflow.

End RamBadState.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_bad_state" RamBadState.
