(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Merged jump target tests: collection, region checking, JMS, and JUN targets. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module JumpTargets.

(* Jump target collection *)
Inductive instr_collection : Type :=
| JUN_coll : nat -> instr_collection
| JMS_coll : nat -> instr_collection
| NOP_coll : instr_collection.

Definition jump_target_collection (i : instr_collection) : option nat :=
  match i with
  | JUN_coll a => Some a
  | JMS_coll a => Some a
  | NOP_coll => None
  end.

Fixpoint collect_targets (prog : list instr_collection) : list nat :=
  match prog with
  | [] => []
  | i :: rest =>
      match jump_target_collection i with
      | Some a => a :: collect_targets rest
      | None => collect_targets rest
      end
  end.

Definition test_collection : nat :=
  length (collect_targets [JUN_coll 17; NOP_coll; JMS_coll 511; NOP_coll]).

(* Jump target region check *)
Inductive instr_region : Type :=
| JUN_reg : nat -> instr_region
| JMS_reg : nat -> instr_region
| NOP_reg : instr_region.

Record layout : Type := MkLayout {
  base' : nat;
  code_ : nat
}.

Definition addr_in_region (addr : nat) (l : layout) : bool :=
  (Nat.leb (base' l) addr) && (Nat.ltb addr (base' l + code_ l)).

Definition jump_target_region (i : instr_region) : option nat :=
  match i with
  | JUN_reg a => Some a
  | JMS_reg a => Some a
  | NOP_reg => None
  end.

Definition in_layout (l : layout) (i : instr_region) : bool :=
  match jump_target_region i with
  | Some a => addr_in_region a l
  | None => true
  end.

Definition test_region_check : bool :=
  in_layout (MkLayout 16 32) (JUN_reg 40).

(* Jump target from JMS *)
Inductive instr_jms : Type :=
| JUN_jms : nat -> instr_jms
| JMS_jms : nat -> instr_jms
| NOP_jms : instr_jms.

Definition jump_target_jms (i : instr_jms) : option nat :=
  match i with
  | JUN_jms a => Some a
  | JMS_jms a => Some a
  | NOP_jms => None
  end.

Definition option_nat_or_zero (o : option nat) : nat :=
  match o with
  | Some n => n
  | None => 0
  end.

Definition test_jms : nat :=
  option_nat_or_zero (jump_target_jms (JMS_jms 144)).

(* Jump target from JUN *)
Inductive instr_jun : Type :=
| JUN_jun : nat -> instr_jun
| JMS_jun : nat -> instr_jun
| NOP_jun : instr_jun.

Definition jump_target_jun (i : instr_jun) : option nat :=
  match i with
  | JUN_jun a => Some a
  | JMS_jun a => Some a
  | NOP_jun => None
  end.

Definition target_default (o : option nat) : nat :=
  match o with
  | Some a => a
  | None => 0
  end.

Definition test_jun : nat :=
  target_default (jump_target_jun (JUN_jun 511)).

(* Combined test result as tuple *)
Definition t : nat * bool * nat * nat :=
  (test_collection, test_region_check, test_jms, test_jun).

End JumpTargets.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "jump_targets" JumpTargets.
