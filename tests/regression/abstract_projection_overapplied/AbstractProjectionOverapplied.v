(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a projection of a record declared in a module type, whose field
    is a function, applied to more arguments than the projection takes.  In
    the functor body [X.step X.a (X.base X.a)] projects [step] and applies
    the function it holds; the projection is printed as an accessor lambda
    and the extra argument is passed to that lambda along with the record:
    [[](const auto &_x) { return _x.step; }(X::a, X::a.base)], "no
    matching function for call".  A record declared outside a module type
    applies the extra argument to the field's value. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module AbstractProjectionOverapplied.

Module Type T.
  Record alg := { step : nat -> nat; base : nat }.
  Parameter a : alg.
End T.

Module Impl <: T.
  Record alg := { step : nat -> nat; base : nat }.
  Definition a : alg := {| step := S; base := 3 |}.
End Impl.

Module Use (X : T). Definition go : nat := X.step X.a (X.base X.a). End Use.

Module U := Use Impl.

Definition result : nat := U.go.

End AbstractProjectionOverapplied.

Crane Extraction "abstract_projection_overapplied" AbstractProjectionOverapplied.
