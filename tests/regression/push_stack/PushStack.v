(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral: pushing onto empty yields length 1, overflow keeps depth 3 with new addr at top. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module PushStack.

Record state : Type := mkState {
  stack : list nat
}.

Definition push_stack (s : state) (addr : nat) : state :=
  match stack s with
  | [] => mkState [addr]
  | x :: [] => mkState [addr; x]
  | x :: y :: [] => mkState [addr; x; y]
  | x :: y :: _ => mkState [addr; x; y]
  end.

Definition top_or_zero (s : state) : nat :=
  match stack s with
  | [] => 0
  | x :: _ => x
  end.

(* Pushing onto empty stack yields length 1 *)
Definition empty_len : nat := length (stack (push_stack (mkState []) 12)).

(* Pushing onto full stack places new address at top *)
Definition overflow_head : nat := top_or_zero (push_stack (mkState [1; 2; 3]) 9).

(* Pushing onto full stack keeps depth at 3 *)
Definition overflow_len : nat := length (stack (push_stack (mkState [1; 2; 3]) 9)).

Definition t : nat * nat * nat := (empty_len, overflow_head, overflow_len).

End PushStack.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "push_stack" PushStack.
