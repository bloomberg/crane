(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Inner.z] is a constant, written as a static data member, and [P.z],
    defined in a functor, is written as an accessor.  Inside [F], [I] is an
    alias of [Inner], so [I.z] is [Inner.z], read as a data member; that
    another module has an accessor of the same name says nothing about it. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Module ModuleAliasValueBesideAccessor.

Module Type T.
  Parameter t : Type.
  Parameter z : t.
End T.

Module Outer.
  Module Inner <: T.
    Definition t := nat.
    Definition z := 1.
  End Inner.
  Module P (X : T) <: T.
    Definition t := X.t.
    Definition z := X.z.
  End P.
End Outer.

Module F (X : T).
  Module I := Outer.Inner.
  Definition get := I.z.
End F.

Module FN := F Outer.Inner.
Module PN := Outer.P Outer.Inner.
Definition from_alias : nat := FN.get.
Definition from_accessor : nat := PN.z.

End ModuleAliasValueBesideAccessor.

Crane Extraction "module_alias_value_beside_accessor" ModuleAliasValueBesideAccessor.
