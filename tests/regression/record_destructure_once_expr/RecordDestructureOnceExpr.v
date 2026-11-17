(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a record taken apart where an expression is expected -- here
    a constructor's argument -- was generated as one declaration per field,
    each evaluating the record's expression afresh, so a function taking its
    own recursive result apart into three fields made three recursive calls
    at every level.  [count 40] made 3^40 calls.  The statement form was
    fixed before; see [record_destructure_once]. *)

From Stdlib Require Import Nat.

Module RecordDestructureOnceExpr.

Record triple : Type := Mk { t_steps : nat; t_twice : nat; t_zero : nat }.

Fixpoint count (n : nat) : triple :=
  match n with
  | O => Mk 0 0 0
  | S m => Mk (let (a, b, c) := count m in S (a + b + c)) 0 0
  end.

Definition r_steps : nat := t_steps (count 40).

End RecordDestructureOnceExpr.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "record_destructure_once_expr" RecordDestructureOnceExpr.
