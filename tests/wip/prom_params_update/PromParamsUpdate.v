(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: update PROM parameter fields while preserving others. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PromParamsUpdate.

Record state : Type := mkState {
  acc : nat;
  regs : list nat;
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr : nat) (data : nat) (enable : bool) : state :=
  mkState (acc s) (regs s) (rom s) addr data enable.

Definition t : nat :=
  let s := mkState 3 [1; 2] [9; 8; 7] 0 0 false in
  let s' := set_prom_params s 23 77 true in
  acc s' + prom_addr s' + (if prom_enable s' then prom_data s' else 0).

End PromParamsUpdate.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "prom_params_update" PromParamsUpdate.
