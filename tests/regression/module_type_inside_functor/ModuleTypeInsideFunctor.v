(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a module type declared inside a functor's body is never
    emitted.  [Make]'s body declares [HasF], whose parameter mentions the
    functor parameter's [X.t], and a functor [Apply (Y : HasF)] constrained
    by it; [Make] becomes a class template, inside which a concept cannot be
    declared, and no concept is emitted anywhere else: "unknown type name
    'HasF'".  A module type nested in a plain module works
    ([regression/nested_module_type_concept]). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ModuleTypeInsideFunctor.

Module Type T. Parameter t : Type. Parameter z : t. End T.

Module Make (X : T).
  Module Type HasF. Parameter f : X.t -> nat. End HasF.
  Module Apply (Y : HasF). Definition go : nat := Y.f X.z. End Apply.
End Make.

Module NatT <: T. Definition t := nat. Definition z : nat := 6. End NatT.

Module M1 := Make NatT.
Module F1 <: M1.HasF. Definition f (n : nat) : nat := n + 1. End F1.
Module A1 := M1.Apply F1.

Definition result : nat := A1.go.

End ModuleTypeInsideFunctor.

Crane Extraction "module_type_inside_functor" ModuleTypeInsideFunctor.
