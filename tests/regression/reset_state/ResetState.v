(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Reset state operations: clearing CPU fields and preserving memory. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ResetState.

(* Full state with all fields *)
Record state_full : Type := mkStateFull {
  acc : nat;
  regs_full : list nat;
  carry : bool;
  pc_full : nat;
  stack : list nat;
  ram_sys : list nat;
  rom : list nat
}.

(* Minimal state without accumulator *)
Record state_minimal : Type := mkStateMinimal {
  regs_minimal : list nat;
  carry_minimal : bool;
  pc_minimal : nat;
  ram_sys_minimal : list nat;
  rom_minimal : list nat
}.

(* ===== Reset with memory preservation ===== *)

Definition reset_state_full (s : state_full) : state_full :=
  mkStateFull 0 (regs_full s) false 0 [] (ram_sys s) (rom s).

Definition memory_preserve_test : nat :=
  let s := mkStateFull 9 [1; 2] true 55 [8; 7] [3; 4; 5] [10; 11] in
  let s' := reset_state_full s in
  acc s' + nth 1 (ram_sys s') 0 + nth 0 (rom s') 0 + length (stack s').

(* ===== Reset clearing PC ===== *)

Definition reset_state_minimal (s : state_minimal) : state_minimal :=
  mkStateMinimal (regs_minimal s) false 0 (ram_sys_minimal s) (rom_minimal s).

Definition pc_clear_test : nat :=
  pc_minimal (reset_state_minimal (mkStateMinimal [1; 2] true 99 [3] [4; 5])).

(* ===== Combined test output ===== *)

Definition t : nat * nat := (memory_preserve_test, pc_clear_test).

End ResetState.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "reset_state" ResetState.
