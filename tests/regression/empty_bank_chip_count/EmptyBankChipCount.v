(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: empty bank allocates NCHIPS chip slots. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module EmptyBankChipCount.

Record ram_reg : Type := mkRAMReg {
  reg_main : list nat;
  reg_status : list nat
}.

Record ram_chip : Type := mkRAMChip {
  chip_regs : list ram_reg;
  chip_port : nat
}.

Record ram_bank : Type := mkRAMBank {
  bank_chips : list ram_chip
}.

Definition NREGS := 4.
Definition NMAIN := 16.
Definition NSTAT := 4.
Definition NCHIPS := 4.

Definition empty_reg : ram_reg := mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT).
Definition empty_chip : ram_chip := mkRAMChip (repeat empty_reg NREGS) 0.
Definition empty_bank : ram_bank := mkRAMBank (repeat empty_chip NCHIPS).

Definition t : nat := length (bank_chips empty_bank).

End EmptyBankChipCount.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "empty_bank_chip_count" EmptyBankChipCount.
