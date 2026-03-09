(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Consolidated test: RAM empty/default constructors. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamEmptyWf.

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

Definition empty_reg : ram_reg := mkReg (repeat 0 16) (repeat 0 4).
Definition empty_chip : ram_chip := mkChip (repeat empty_reg 4) 0.
Definition empty_bank : ram_bank := mkBank (repeat empty_chip 4).
Definition empty_ram : list ram_bank := repeat empty_bank 4.
Definition default_sel : ram_sel := mkSel 0 0 0 0.

Definition default_bank_idx : nat := sel_bank default_sel.

End RamEmptyWf.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_empty_wf" RamEmptyWf.
