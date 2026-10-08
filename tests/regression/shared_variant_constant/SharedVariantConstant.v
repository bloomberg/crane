(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane SharedVariant]: a closed constructor term -- a [positive]
    literal inside a function -- is built once and kept, so evaluating it
    again copies the same block rather than allocating, and every block it
    holds is immortal.  Arithmetic over the constants is unchanged. *)

From Stdlib Require Import BinPos.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedVariantConstant.

Definition seven (u : unit) : positive := 7%positive.

Definition pair_of (u : unit) : positive * positive := (6%positive, 12%positive).

Definition add_ten (p : positive) : positive := Pos.add p 10.

Fixpoint sum_tens (n : nat) (acc : positive) : positive :=
  match n with O => acc | S m => sum_tens m (add_ten acc) end.

Definition result : positive := sum_tens 100 1.

End SharedVariantConstant.

Set Crane SharedVariant.
Crane Extraction "shared_variant_constant" SharedVariantConstant.
