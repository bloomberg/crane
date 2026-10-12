(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: two module types with the same short name, declared in
    different modules, become two C++ concepts with the same name.  A
    concept cannot be declared inside a struct, so each is emitted at
    namespace scope under its short name, [T]: "redefinition of concept 'T'
    with different template parameters or requirements".  The standard
    library hits it when [FMapList] and [MSetList] are used together: the
    two libraries' [OrderedType] module types clash. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeShortNameClash.

Module A.
  Module Type T. Parameter x : nat. End T.
  Module F (X : T). Definition get : nat := X.x + 1. End F.
End A.

Module B.
  Module Type T. Parameter y : bool. End T.
  Module F (X : T). Definition get : nat := if X.y then 1 else 0. End F.
End B.

Module IA <: A.T. Definition x := 4. End IA.
Module IB <: B.T. Definition y := true. End IB.

Module FA := A.F IA.
Module FB := B.F IB.

Definition result : nat := FA.get + FB.get.

End ModuleTypeShortNameClash.

Crane Extraction "module_type_short_name_clash" ModuleTypeShortNameClash.
