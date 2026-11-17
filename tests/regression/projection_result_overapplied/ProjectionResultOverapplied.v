(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: the function held in a pair, projected with [fst] or [snd] and
    applied to two arguments, is called one argument at a time.  Under
    [Mapping.Std] the projection is the inline text [%a0.first], and the
    arguments it is over-applied to are applied after it one by one --
    [fp.first(2)(3)] -- while the component is a flat
    [crane::fn<uint64_t(uint64_t, uint64_t)>]: "no matching function for
    call".  The same function in an [option], applied after a match, is
    called flat. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ProjectionResultOverapplied.

Definition fp : (nat -> nat -> nat) * nat := (Nat.add, 0).

Definition direct : nat := fst fp 2 3.

Definition getf (p : (nat -> nat -> nat) * nat) := fst p.
Definition through_definition : nat := getf fp 2 3.

Definition apply_snd (p : nat * (nat -> nat -> nat)) : nat := (snd p) (fst p) 10.
Definition second : nat := apply_snd (4, Nat.mul).

End ProjectionResultOverapplied.

Crane Extraction "projection_result_overapplied" ProjectionResultOverapplied.
