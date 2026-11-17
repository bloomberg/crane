(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Mapping.NInt] converts [N.to_nat] to [unsigned int], whatever
    [nat] is represented as.  Under [Mapping.NatIntStd] a [nat] is a
    [uint64_t], so [Nat.max (N.to_nat n) 5] -- [std::max] of an
    [unsigned int] and a [uint64_t] -- cannot deduce one type: "no matching
    function for call to 'max'", and the same for [min]. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import NArith.
From Crane Require Import Mapping.NInt.

Module NToNatRepresentation.

Definition n : N := 300%N.

Definition larger : nat := Nat.max (N.to_nat n) 5.
Definition smaller : nat := Nat.min 7 (N.to_nat n).
Definition mapped : nat := fold_left Nat.add (List.map N.to_nat [1%N; 2%N]) 0.

End NToNatRepresentation.

Crane Extraction "n_to_nat_representation" NToNatRepresentation.
