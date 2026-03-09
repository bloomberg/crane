(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: RAM init/reset state. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamInitReset.

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

Definition init_state : state :=
  mkState (repeat 0 16) 0 false 0 [] empty_ram default_sel (repeat 0 8).

Definition reset_state (s : state) : state :=
  mkState (state_regs s) 0 false 0 [] (state_ram s) default_sel (state_rom s).

Definition pop_stack (s : state) : option nat * state :=
  match state_stack s with
  | [] => (None, s)
  | x :: xs =>
      (Some x,
       mkState (state_regs s) (state_acc s) (state_carry s) (state_pc s)
               xs (state_ram s) (state_sel s) (state_rom s))
  end.

Definition reset_pc : nat := state_pc (reset_state init_state).

End RamInitReset.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_init_reset" RamInitReset.
