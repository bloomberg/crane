(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: RAM write operations. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamWrite.

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

Definition get_main (rg : ram_reg) (i : nat) : nat :=
  nth i (reg_main rg) 0.

Definition upd_main_in_reg (rg : ram_reg) (i v : nat) : ram_reg :=
  mkReg (update_nth i (v mod 16) (reg_main rg)) (reg_status rg).

Definition upd_stat_in_reg (rg : ram_reg) (i v : nat) : ram_reg :=
  mkReg (reg_main rg) (update_nth i (v mod 16) (reg_status rg)).

Definition get_regRAM (ch : ram_chip) (r : nat) : ram_reg :=
  nth r (chip_regs ch) empty_reg.

Definition upd_reg_in_chip (ch : ram_chip) (r : nat) (rg : ram_reg) : ram_chip :=
  mkChip (update_nth r rg (chip_regs ch)) (chip_port ch).

Definition get_chip (bk : ram_bank) (c : nat) : ram_chip :=
  nth c (bank_chips bk) empty_chip.

Definition upd_chip_in_bank (bk : ram_bank) (c : nat) (ch : ram_chip) : ram_bank :=
  mkBank (update_nth c ch (bank_chips bk)).

Definition get_bank_from_sys (sys : list ram_bank) (b : nat) : ram_bank :=
  nth b sys empty_bank.

Definition upd_bank_in_sys (s : state) (b : nat) (bk : ram_bank) : list ram_bank :=
  update_nth b bk (state_ram s).

Definition current_bank (s : state) : ram_bank :=
  get_bank_from_sys (state_ram s) (sel_bank (state_sel s)).

Definition current_chip (s : state) : ram_chip :=
  get_chip (current_bank s) (sel_chip (state_sel s)).

Definition current_reg (s : state) : ram_reg :=
  get_regRAM (current_chip s) (sel_reg (state_sel s)).

Definition ram_read_main (s : state) : nat :=
  get_main (current_reg s) (sel_char (state_sel s)).

Definition ram_write_main_sys (s : state) (v : nat) : list ram_bank :=
  let rg := current_reg s in
  let ch := current_chip s in
  let bk := current_bank s in
  let rg' := upd_main_in_reg rg (sel_char (state_sel s)) v in
  let ch' := upd_reg_in_chip ch (sel_reg (state_sel s)) rg' in
  let bk' := upd_chip_in_bank bk (sel_chip (state_sel s)) ch' in
  upd_bank_in_sys s (sel_bank (state_sel s)) bk'.

Definition ram_write_status_sys (s : state) (idx v : nat) : list ram_bank :=
  let rg := current_reg s in
  let ch := current_chip s in
  let bk := current_bank s in
  let rg' := upd_stat_in_reg rg idx v in
  let ch' := upd_reg_in_chip ch (sel_reg (state_sel s)) rg' in
  let bk' := upd_chip_in_bank bk (sel_chip (state_sel s)) ch' in
  upd_bank_in_sys s (sel_bank (state_sel s)) bk'.

Definition write_bank_count : nat := length (ram_write_main_sys init_state 12).

End RamWrite.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_write" RamWrite.
