(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: reset_state clears program counter to zero. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ExecuteCmcWfBehavior0100.

Record state : Type := mkState {
  regs : list nat;
  carry : bool;
  pc : nat;
  ram_sys : list nat;
  rom : list nat
}.

Definition reset_state (s : state) : state :=
  mkState (regs s) false 0 (ram_sys s) (rom s).

Definition t : nat :=
  pc (reset_state (mkState [1; 2] true 99 [3] [4; 5])).

End ExecuteCmcWfBehavior0100.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "execute_cmc_wf_behavior_0100" ExecuteCmcWfBehavior0100.
