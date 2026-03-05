(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: read selected RAM main nibble via bank/chip/reg selectors. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module RamReadMainSelector.

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
  sel_chip : nat;
  sel_reg : nat;
  sel_char : nat
}.

Record state : Type := mkState {
  ram_sys : list ram_bank;
  cur_bank : nat;
  sel_ram : ram_sel
}.

Definition empty_reg : ram_reg := mkReg [] [].
Definition empty_chip : ram_chip := mkChip [] 0.
Definition empty_bank : ram_bank := mkBank [].

Definition get_bank (s : state) (b : nat) : ram_bank :=
  nth b (ram_sys s) empty_bank.

Definition get_chip (bk : ram_bank) (c : nat) : ram_chip :=
  nth c (bank_chips bk) empty_chip.

Definition get_regRAM (ch : ram_chip) (r : nat) : ram_reg :=
  nth r (chip_regs ch) empty_reg.

Definition get_main (rg : ram_reg) (i : nat) : nat :=
  nth i (reg_main rg) 0.

Definition ram_read_main (s : state) : nat :=
  let bk := get_bank s (cur_bank s) in
  let ch := get_chip bk (sel_chip (sel_ram s)) in
  let rg := get_regRAM ch (sel_reg (sel_ram s)) in
  get_main rg (sel_char (sel_ram s)).

Definition sample_reg : ram_reg := mkReg [5; 6; 7; 8] [0; 0; 0; 0].
Definition sample_chip : ram_chip := mkChip [sample_reg] 3.
Definition sample_bank : ram_bank := mkBank [sample_chip].
Definition sample_sel : ram_sel := mkSel 0 0 2.
Definition sample_state : state := mkState [sample_bank] 0 sample_sel.

Definition t : nat := ram_read_main sample_state.

End RamReadMainSelector.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_read_main_selector" RamReadMainSelector.
