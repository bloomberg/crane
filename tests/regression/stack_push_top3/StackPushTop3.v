(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: cap stack growth to top 3 entries on push. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module StackPushTop3.

Record state : Type := mkState {
  stack : list nat
}.

Definition push_stack (s : state) (addr : nat) : state :=
  let new_stack :=
    match stack s with
    | [] => [addr]
    | [a] => [addr; a]
    | [a; b] => [addr; a; b]
    | a :: b :: c :: _ => [addr; a; b]
    end in
  mkState new_stack.

Definition t : nat :=
  length (stack (push_stack (mkState [10; 20; 30; 40]) 7)).

End StackPushTop3.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "stack_push_top3" StackPushTop3.
