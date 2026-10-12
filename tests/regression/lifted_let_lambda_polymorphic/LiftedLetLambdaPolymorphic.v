(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a local function bound by [let] in a polymorphic definition,
    and applied there to fewer arguments than it takes, is lifted to a
    helper whose template parameters the call cannot deduce.  [compose] in
    [all] becomes [template <T1, T2, T3, F0, F1> T2 all_crane_compose(F0&&,
    F1&&, const T3)]: [T1] occurs only in a [requires] clause, and the
    partial application [compose op op] passes no explicit type arguments,
    so "no matching function for call to 'all_crane_compose'".  The
    monomorphic version compiles.  A section [Let] is the same lift, so
    [quad] and [all] in section [S] fail the same way. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LiftedLetLambdaPolymorphic.

Definition all {A : Type} (op : A -> A) : list (A -> A) :=
  let compose (f g : A -> A) := fun x => f (g x) in
  [compose op op; op].

Definition from_let : nat := fold_left (fun a f => f a) (all (Nat.mul 2)) 1.

Section S.
  Variable B : Type.
  Variable op : B -> B -> B.
  Let twice := fun x => op x x.
  Let compose (f g : B -> B) := fun x => f (g x).
  Definition quad := compose twice twice.
End S.

Definition from_section : nat := quad nat Nat.add 1.

End LiftedLetLambdaPolymorphic.

Crane Extraction "lifted_let_lambda_polymorphic" LiftedLetLambdaPolymorphic.
