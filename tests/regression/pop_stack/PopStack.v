(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral: popping an empty stack yields None, popping nonempty returns top. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PopStack.

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

Definition option_or_zero (o : option nat) : nat :=
  match o with
  | Some n => n
  | None => 0
  end.

(* Popping empty stack yields None *)
Definition empty_is_none : bool := is_none (fst (pop_stack (mkState []))).

(* Popping nonempty stack returns the top address *)
Definition some_addr : nat := option_or_zero (fst (pop_stack (mkState [9; 8]))).

Definition t : nat * bool := (some_addr, empty_is_none).

End PopStack.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "pop_stack" PopStack.
