(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module type's [Parameter] whose type mentions an enum the
    module type declares is required with the enum misspelled.  The enum is
    declared [enum class Color] and the concept requires [typename
    M::Color] for the type itself
    ([regression/module_type_enum_concept]), but the requirement for
    [paint : color -> t -> t] prints its parameter types with the Rocq
    spelling: [M::paint(std::declval<typename M::color>(), ...)], "no type
    named 'color'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeEnumInParameter.

Module Type T.
  Inductive color := Red | Green | Blue.
  Parameter t : Type.
  Parameter paint : color -> t -> t.
  Parameter base : t.
End T.

Module Impl <: T.
  Inductive color := Red | Green | Blue.
  Definition t := nat.
  Definition paint (c : color) (n : t) : t :=
    match c with Red => n + 1 | Green => n + 2 | Blue => n + 3 end.
  Definition base : t := 0.
End Impl.

Module Use (X : T). Definition go := X.paint X.Blue (X.paint X.Red X.base). End Use.

Module U := Use Impl.

Definition result : nat := U.go.

End ModuleTypeEnumInParameter.

Crane Extraction "module_type_enum_in_parameter" ModuleTypeEnumInParameter.
