(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: build ISZ loop-test instruction target. *)

From Stdlib Require Import Nat.

Module CountLoopTestTarget.

Inductive instruction : Type :=
| ISZ : nat -> nat -> instruction
| NOP : instruction.

Definition count_loop_test (loop_addr : nat) : instruction :=
  ISZ 0 loop_addr.

Definition target_of (i : instruction) : nat :=
  match i with
  | ISZ _ a => a
  | NOP => 0
  end.

Definition t : nat := target_of (count_loop_test 37).

End CountLoopTestTarget.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "count_loop_test_target" CountLoopTestTarget.
