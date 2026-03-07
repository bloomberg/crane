(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: popping an empty stack yields no address. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PopStackEmptyIsNone.

Record state : Type := mkState {
  stack : list nat
}.

Definition pop_stack (s : state) : option nat * state :=
  match stack s with
  | [] => (None, s)
  | x :: xs => (Some x, mkState xs)
  end.

Definition is_none (o : option nat) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition t : bool := is_none (fst (pop_stack (mkState []))).

End PopStackEmptyIsNone.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "pop_stack_empty_is_none" PopStackEmptyIsNone.
