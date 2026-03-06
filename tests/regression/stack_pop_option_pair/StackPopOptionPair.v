(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: pop stack to option-value and next state pair. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module StackPopOptionPair.

Record state : Type := mkState {
  stack : list nat;
  acc : nat
}.

Definition pop_stack (s : state) : option nat * state :=
  match stack s with
  | [] => (None, s)
  | a :: rest => (Some a, mkState rest (acc s))
  end.

Definition t : nat :=
  match pop_stack (mkState [9; 8] 3) with
  | (Some a, s') => a + length (stack s') + acc s'
  | (None, s') => acc s'
  end.

End StackPopOptionPair.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "stack_pop_option_pair" StackPopOptionPair.
