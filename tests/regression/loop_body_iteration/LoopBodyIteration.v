(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: iterate_body count-loop style update. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module LoopBodyIteration.

Record state : Type := MkState {
  regs_ : list nat
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition get_reg0 (s : state) : nat := nth 0 (regs_ s) 0.

Definition count_loop_body (s : state) : state :=
  MkState (update_nth 0 ((get_reg0 s + 1) mod 16) (regs_ s)).

Fixpoint iterate_body (n : nat) (s : state) : state :=
  match n with
  | 0 => s
  | S n' => iterate_body n' (count_loop_body s)
  end.

Definition sample : state := MkState [0; 1; 2].
Definition t : nat := get_reg0 (iterate_body 5 sample).

End LoopBodyIteration.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "loop_body_iteration" LoopBodyIteration.
