(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: single-step fetch-decode-execute composition. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module StepFetchDecodeExec.

Inductive instruction : Type :=
| NOP : instruction
| ADD_ACC : nat -> instruction.

Record state : Type := mkState {
  acc : nat;
  pc : nat;
  rom : list nat
}.

Definition fetch_byte (s : state) (addr : nat) : nat :=
  nth addr (rom s) 0.

Definition decode (b1 : nat) (b2 : nat) : instruction :=
  if b1 mod 2 =? 0 then NOP else ADD_ACC (b2 mod 16).

Definition execute (s : state) (i : instruction) : state :=
  match i with
  | NOP => mkState (acc s) (pc s + 1) (rom s)
  | ADD_ACC n => mkState ((acc s + n) mod 16) (pc s + 2) (rom s)
  end.

Definition step (s : state) : state :=
  let b1 := fetch_byte s (pc s) in
  let b2 := fetch_byte s (pc s + 1) in
  execute s (decode b1 b2).

Definition t : nat :=
  let s1 := step (mkState 3 0 [1; 6; 0]) in
  acc s1 + pc s1.

End StepFetchDecodeExec.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "step_fetch_decode_exec" StepFetchDecodeExec.
