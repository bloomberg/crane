(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: ISZ loop/terminate flag evaluation from register value. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module IszLoopFlags.

Definition nibble_of_nat (n : nat) : nat := n mod 16.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat :=
  nth r (regs s) 0.

Definition isz_loops (s : state) (r : nat) : bool :=
  negb (nibble_of_nat (get_reg s r + 1) =? 0).

Definition isz_terminates (s : state) (r : nat) : bool :=
  nibble_of_nat (get_reg s r + 1) =? 0.

Definition t : nat :=
  let s := mkState [15; 3] in
  (if isz_loops s 0 then 1 else 0) +
  (if isz_terminates s 0 then 1 else 0).

End IszLoopFlags.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "isz_loop_flags" IszLoopFlags.
