(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: popping a nonempty stack returns the top address. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module PopStackSomeAddr.

Record state : Type := mkState {
  stack : list nat
}.

Definition pop_stack (s : state) : option nat * state :=
  match stack s with
  | [] => (None, s)
  | x :: xs => (Some x, mkState xs)
  end.

Definition option_or_zero (o : option nat) : nat :=
  match o with
  | Some n => n
  | None => 0
  end.

Definition t : nat := option_or_zero (fst (pop_stack (mkState [9; 8]))).

End PopStackSomeAddr.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "pop_stack_some_addr" PopStackSomeAddr.
