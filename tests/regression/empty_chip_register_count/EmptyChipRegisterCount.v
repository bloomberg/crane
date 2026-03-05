(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: empty chip allocates NREGS register slots. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module EmptyChipRegisterCount.

Record ram_reg : Type := mkRAMReg {
  reg_main : list nat;
  reg_status : list nat
}.

Record ram_chip : Type := mkRAMChip {
  chip_regs : list ram_reg;
  chip_port : nat
}.

Definition NREGS := 4.
Definition NMAIN := 16.
Definition NSTAT := 4.

Definition empty_reg : ram_reg := mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT).
Definition empty_chip : ram_chip := mkRAMChip (repeat empty_reg NREGS) 0.

Definition t : nat := length (chip_regs empty_chip).

End EmptyChipRegisterCount.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "empty_chip_register_count" EmptyChipRegisterCount.
