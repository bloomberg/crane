(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Crane Extraction Implicit] erases an argument a call still passes: it
    decides the binder's role, not which scheme variable comes from which
    binder.  A declared-implicit binder ahead of a type binder must not take
    that binder's variable, and one declared on a type binder leaves the
    variable where type extraction put it.
    - [sel {A} (tag : bool) {B}] with [tag] implicit: [A] and [B] keep their
      variables, and [B] is still the result's.
    - [nil_of {A} (tag : nat) {B}] mentions [B] only in its result, so the
      call must name it, at [B]'s own variable.
    - [both {A} (tag : nat) {B}] has [A] declared implicit too. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TyargImplicitTypeBinder.

Definition sel {A : Type} (tag : bool) {B : Type} (a : A) (b : B) : B := b.

Definition selected : nat := sel true 3 4.

Definition nil_of {A : Type} (tag : nat) {B : Type} (a : A) : list B := [].

Definition nil_len : nat := length (@nil_of nat 0 bool 3).

Definition both {A : Type} (tag : nat) {B : Type} (a : A) (b : B) : A * B := (a, b).

Definition both_fst : nat := fst (both 1 2 true).

End TyargImplicitTypeBinder.

Crane Extraction Implicit TyargImplicitTypeBinder.sel [ tag ].
Crane Extraction Implicit TyargImplicitTypeBinder.nil_of [ tag ].
Crane Extraction Implicit TyargImplicitTypeBinder.both [ A tag ].
Crane Extraction "tyarg_implicit_type_binder" TyargImplicitTypeBinder.
