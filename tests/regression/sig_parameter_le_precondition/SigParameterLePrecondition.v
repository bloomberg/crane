(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a [sig] parameter whose predicate is [m <= n] trips
    [-Werror,-Wunused-parameter].  The predicate is rendered into a
    precondition comment through [le]'s mapping template, which names [n]
    [_x] for the comment and leaves a [%1] placeholder unsubstituted --
    [// Precondition: _x <= %1] -- and [_x], which the body never reads, is
    left as a named parameter: "unused parameter '_x'".  [{m | m + k <= n}]
    leaves the parameter unnamed and compiles. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SigParameterLePrecondition.

Definition get (n : nat) (b : { m : nat | m <= n }) : nat := proj1_sig b.

Definition get2 (n : nat) (b : { m : nat | n <= m }) : nat := proj1_sig b.

Definition result : nat :=
  get 5 (exist _ 3 (le_S _ _ (le_S _ _ (le_n 3)))) + get2 0 (exist _ 2 (le_0_n 2)).

End SigParameterLePrecondition.

Crane Extraction "sig_parameter_le_precondition" SigParameterLePrecondition.
