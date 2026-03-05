(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: init_state provisions 16 general registers. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module InitStateRegisterCount.

Record state : Type := mkState {
  regs : list nat;
  rom : list nat
}.

Definition init_state : state := mkState (repeat 0 16) (repeat 0 4096).

Definition t : nat := length (regs init_state).

End InitStateRegisterCount.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "init_state_register_count" InitStateRegisterCount.
