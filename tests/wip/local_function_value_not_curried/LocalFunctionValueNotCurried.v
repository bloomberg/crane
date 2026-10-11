(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a local function of type [nat -> nat -> nat], passed unapplied
    where a [nat -> (nat -> nat)] is expected, is not curried to the slot.
    A global, a class method and a [let]-bound [fun a b => ...] are curried
    there; two other local functions are passed flat:
    - a [let fix] whose body returns [fun x => ...], emitted as a flat
      two-argument lambda, given to [List.map mk l] at [list (nat -> nat)];
    - a function parameter [f : nat -> nat -> nat] in [List.map f l].
    Both are "no matching member function for call to 'map'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LocalFunctionValueNotCurried.

Definition from_fix (l : list nat) : list (nat -> nat) :=
  let fix mk (n : nat) : nat -> nat :=
    match n with 0 => fun x => x | S k => fun x => S (mk k x) end in
  List.map mk l.

Definition from_param (f : nat -> nat -> nat) (l : list nat) : list (nat -> nat) := List.map f l.

Definition result : nat :=
  fold_left (fun a h => h a) (from_fix [1; 2]) 0
  + fold_left (fun a h => h a) (from_param Nat.add [1; 2]) 0.

End LocalFunctionValueNotCurried.

Crane Extraction "local_function_value_not_curried" LocalFunctionValueNotCurried.
