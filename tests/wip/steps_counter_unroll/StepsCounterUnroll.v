(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: tail-recursive step counter unrolling. *)

From Stdlib Require Import Nat.

Module StepsCounterUnroll.

Record state : Type := mkState {
  pc : nat
}.

Definition step (s : state) : state :=
  mkState ((pc s + 1) mod 4096).

Fixpoint steps (n : nat) (s : state) : state :=
  match n with
  | 0 => s
  | S n' => steps n' (step s)
  end.

Definition t : nat :=
  pc (steps 5 (mkState 4094)).

End StepsCounterUnroll.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "steps_counter_unroll" StepsCounterUnroll.
