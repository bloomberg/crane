(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined test: init_state properties. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module InitStateProps.

(* === Full state record with both regs and rom === *)

Record state : Type := mkState {
  regs : list nat;
  rom : list nat
}.

Definition init_state : state := mkState (repeat 0 16) (repeat 0 4096).

(* === From init_state_register_count === *)

Definition test_register_count : nat := length (regs init_state).

(* === From init_state_rom_length === *)

Definition test_rom_length : nat := length (rom init_state).

(* Combined test tuple *)
Definition t : nat * nat :=
  (test_register_count, test_rom_length).

End InitStateProps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "init_state_props" InitStateProps.
