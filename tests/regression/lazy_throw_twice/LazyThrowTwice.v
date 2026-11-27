(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A suspension whose computation throws is forced twice.  Its thunk runs
    once and may move out of what it captured before it throws, so a second
    force must not run it again: the exception is kept and rethrown.  [boom]
    is an axiom, which throws when called. *)
Require Import Crane.Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

Module LazyThrowTwice.

Axiom boom : list nat -> nat.

CoInductive stream : Type :=
| SCons : nat -> stream -> stream.

CoFixpoint after (l : list nat) : stream :=
  SCons (boom l) (after (length l :: l)).

CoFixpoint upto (n : nat) (l : list nat) : stream :=
  match n with
  | O => after l
  | S m => SCons (length l) (upto m (n :: l))
  end.

Definition hd (s : stream) : nat :=
  match s with
  | SCons x _ => x
  end.

Definition tl (s : stream) : stream :=
  match s with
  | SCons _ xs => xs
  end.

Definition sample (u : unit) : stream := upto 1 [1; 2; 3].

End LazyThrowTwice.

Crane Extraction "lazy_throw_twice" LazyThrowTwice.
