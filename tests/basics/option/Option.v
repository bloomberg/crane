(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test extraction of option type to std::optional *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module Option.

(* Test option construction *)
Definition some_val : option nat := Some five.
Definition none_val : option nat := None.

(* Test option pattern matching *)
Definition get_or_default (o : option nat) (default : nat) : nat :=
  match o with
  | Some x => x
  | None => default
  end.

(* Test nested options *)
Definition nested_some : option (option nat) := Some (Some three).
Definition nested_none : option (option nat) := Some None.

(* Test option in function results *)
Definition safe_pred (n : nat) : option nat :=
  match n with
  | O => None
  | S m => Some m
  end.

(* Test chaining option operations *)
Definition chain_options (o1 o2 : option nat) : option nat :=
  match o1 with
  | None => o2
  | Some _ => o1
  end.

(* Test option with function types *)
Definition apply_if_some {A B : Type} (f : option (A -> B)) (x : A) : option B :=
  match f with
  | None => None
  | Some g => Some (g x)
  end.

(* Test values for verification *)
Definition test_some := get_or_default some_val zero.
Definition test_none := get_or_default none_val zero.
Definition test_pred_zero := safe_pred zero.
Definition test_pred_five := safe_pred five.

End Option.

Crane Extraction "option" Option.
