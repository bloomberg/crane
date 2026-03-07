(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: pushing onto an empty stack yields length one. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module PushStackEmptyLen.

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

Definition t : nat := length (stack (push_stack (mkState []) 12)).

End PushStackEmptyLen.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "push_stack_empty_len" PushStackEmptyLen.
