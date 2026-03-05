(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: set PROM parameters on large machine-state record. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PromParamsLargeState.

Record state : Type := mkState {
  acc : nat;
  regs : list nat;
  carry : bool;
  pc : nat;
  stack : list nat;
  ram_sys : list nat;
  cur_bank : nat;
  sel_ram : nat;
  rom_ports : list nat;
  sel_rom : nat;
  rom : list nat;
  test_pin : bool;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr : nat) (data : nat) (enable : bool) : state :=
  mkState (acc s) (regs s) (carry s) (pc s) (stack s)
          (ram_sys s) (cur_bank s) (sel_ram s)
          (rom_ports s) (sel_rom s) (rom s) (test_pin s)
          addr data enable.

Definition t : nat :=
  let s := mkState 1 [2; 3] false 4 [5] [6] 0 0 [7] 0 [8; 9] true 0 0 false in
  let s' := set_prom_params s 21 144 true in
  prom_addr s' + (if prom_enable s' then prom_data s' else 0) + length (regs s').

End PromParamsLargeState.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prom_params_large_state" PromParamsLargeState.
