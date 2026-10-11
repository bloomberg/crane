(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module type declaring an enum-shaped inductive becomes a
    concept that its implementations cannot satisfy.  The concept requires
    [typename M::color], under the Rocq name, but an enum inductive is
    emitted as [enum class Color], capitalised, so [Use<Impl>] fails its
    constraint: "no type named 'color' in 'Impl'".  The functor body itself
    refers to [X::Color::RED] correctly; only the concept uses the wrong
    name.  A non-enum inductive in a module type works
    ([regression/ind_param]). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeEnumConcept.

Module Type T. Inductive color := Red | Green. End T.

Module Impl <: T. Inductive color := Red | Green. End Impl.

Module Use (X : T).
  Definition f (c : X.color) : nat := match c with X.Red => 1 | X.Green => 2 end.
End Use.

Module U := Use Impl.

Definition result : nat := U.f Impl.Green.

End ModuleTypeEnumConcept.

Crane Extraction "module_type_enum_concept" ModuleTypeEnumConcept.
