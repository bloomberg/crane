(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A class declared inside a submodule has its concept hoisted to file scope,
    because a C++ concept cannot be a class member.  The [static_assert]
    checking the instance is not told about the hoist and still spells the
    concept with the submodule path, [Outer::Inner::C]. *)

Module NestedClassConceptScope.

  Module Outer.
    Module Inner.
      Class C (A : Type) := { m : A -> nat }.
    End Inner.
  End Outer.

  Instance IN : Outer.Inner.C nat := { Outer.Inner.m := fun n => n }.

  Definition test : nat := Outer.Inner.m 5.

End NestedClassConceptScope.

Crane Extraction "nested_class_concept_scope" NestedClassConceptScope.
