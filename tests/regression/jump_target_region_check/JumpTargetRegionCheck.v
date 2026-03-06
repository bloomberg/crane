(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: jump_target and layout region checks. *)

From Stdlib Require Import Bool Nat.

Module JumpTargetRegionCheck.

Inductive instruction : Type :=
| JUN' : nat -> instruction
| JMS_ : nat -> instruction
| NOP_ : instruction.

Record layout : Type := MkLayout {
  base' : nat;
  code_ : nat
}.

Definition addr_in_region (addr : nat) (l : layout) : bool :=
  (Nat.leb (base' l) addr) && (Nat.ltb addr (base' l + code_ l)).

Definition jump_target (i : instruction) : option nat :=
  match i with
  | JUN' a => Some a
  | JMS_ a => Some a
  | NOP_ => None
  end.

Definition in_layout (l : layout) (i : instruction) : bool :=
  match jump_target i with
  | Some a => addr_in_region a l
  | None => true
  end.

Definition t : bool := in_layout (MkLayout 16 32) (JUN' 40).

End JumpTargetRegionCheck.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_target_region_check" JumpTargetRegionCheck.
