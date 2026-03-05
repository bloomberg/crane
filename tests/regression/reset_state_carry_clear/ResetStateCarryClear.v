(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: reset_state clears carry flag. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module ResetStateCarryClear.

Record state : Type := mkState {
  regs : list nat;
  carry : bool;
  pc : nat;
  ram_sys : list nat;
  rom : list nat
}.

Definition reset_state (s : state) : state :=
  mkState (regs s) false 0 (ram_sys s) (rom s).

Definition t : bool :=
  carry (reset_state (mkState [1; 2] true 33 [9] [4; 5])).

End ResetStateCarryClear.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "reset_state_carry_clear" ResetStateCarryClear.
