(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: instruction timing and execution preserve simple state-shape invariants. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module TimingPreservesWfSimple.

Inductive instr : Type :=
| NOP
| ADD
| WRM
| FIM
| JMS.

Record state : Type := mkState {
  regs_len : nat;
  rom_len : nat;
  pc : nat;
  stack_len : nat
}.

Definition wf (s : state) : bool :=
  andb (Nat.eqb (regs_len s) 4)
       (andb (Nat.eqb (rom_len s) 4)
             (andb (Nat.ltb (pc s) 4096)
                   (Nat.leb (stack_len s) 3))).

Definition cycles (i : instr) : nat :=
  match i with
  | NOP | ADD | WRM => 8
  | FIM => 16
  | JMS => 24
  end.

Definition execute (s : state) (i : instr) : state :=
  match i with
  | NOP | ADD | WRM | FIM => mkState (regs_len s) (rom_len s) (pc s) (stack_len s)
  | JMS => mkState (regs_len s) (rom_len s) (pc s) (S (stack_len s))
  end.

Definition sample : state := mkState 4 4 100 2.

Definition t : bool :=
  andb (wf sample)
       (andb (Nat.eqb (cycles JMS) 24)
             (andb (wf (execute sample NOP))
                   (wf (execute sample FIM)))).

End TimingPreservesWfSimple.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "timing_preserves_wf_simple" TimingPreservesWfSimple.
