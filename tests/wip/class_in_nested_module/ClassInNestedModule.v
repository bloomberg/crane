From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** A typeclass becomes a C++ concept, and a module becomes a struct.  A class
    declared inside a module therefore emits a concept inside a struct, which
    C++ allows only at namespace scope; every later reference to the class then
    fails to resolve as well. *)

Module ClassInNestedModule.

  Module Cls.
    Class Show (A : Type) := { sz : A -> nat ; tag : nat }.
    #[export] Instance SN : Show nat := { sz x := x ; tag := 1 }.
  End Cls.

  Import Cls.

  Definition use {A} `{Show A} (x : A) : nat := sz x + tag.

  Definition run : nat := use 5.

End ClassInNestedModule.

Crane Extraction "class_in_nested_module" ClassInNestedModule.
