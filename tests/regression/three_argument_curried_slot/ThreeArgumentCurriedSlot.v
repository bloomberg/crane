(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a function of three arguments passed where a type variable
    stands for its type -- [wrap add3], [idp add3] -- is curried only one
    level.  The slot is [crane::fn<fn<fn<uint64_t(uint64_t)>(uint64_t)>(uint64_t)>],
    and the generated adapter is [[](uint64_t _ec0) { return [=](uint64_t
    _ec1, uint64_t _ec2) { ... }; }]: its inner lambda still takes two
    arguments, and [crane::fn]'s curried call path invokes it with one --
    "no matching function for call to 'invoke'" in [fn.h].  Two arguments
    are curried correctly. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ThreeArgumentCurriedSlot.

Definition idp {A} (x : A) : A := x.
Definition add3 (a b c : nat) : nat := a + b + c.

Definition f3 : nat -> nat -> nat -> nat := idp add3.

Definition wrap {A} (x : A) : list A := [x].
Definition ws : list (nat -> nat -> nat -> nat) := wrap add3.

Definition result : nat := f3 1 2 3 + match ws with g :: _ => g 1 1 1 | [] => 0 end.

End ThreeArgumentCurriedSlot.

Crane Extraction "three_argument_curried_slot" ThreeArgumentCurriedSlot.
