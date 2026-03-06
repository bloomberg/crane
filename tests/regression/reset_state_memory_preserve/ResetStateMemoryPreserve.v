(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: reset clears CPU fields and preserves RAM/ROM payloads. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ResetStateMemoryPreserve.

Record state : Type := mkState {
  acc : nat;
  regs : list nat;
  carry : bool;
  pc : nat;
  stack : list nat;
  ram_sys : list nat;
  rom : list nat
}.

Definition reset_state (s : state) : state :=
  mkState 0 (regs s) false 0 [] (ram_sys s) (rom s).

Definition t : nat :=
  let s := mkState 9 [1; 2] true 55 [8; 7] [3; 4; 5] [10; 11] in
  let s' := reset_state s in
  acc s' + nth 1 (ram_sys s') 0 + nth 0 (rom s') 0 + length (stack s').

End ResetStateMemoryPreserve.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "reset_state_memory_preserve" ResetStateMemoryPreserve.
