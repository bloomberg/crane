(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A constructor's factory method is named by lowercasing the constructor.  For
    [A : nat -> a] that collides with the type name [a], so it is renamed to
    [a0] -- which is exactly the default name given to the constructor's first
    field.  The struct then declares [uint64_t a0] and [static a a0(uint64_t)]. *)

Module FactoryFieldNameClash.

  Inductive a := A : nat -> a.

  Definition get (x : a) : nat := match x with A n => n end.

  Definition test : nat := get (A 1).

End FactoryFieldNameClash.

Crane Extraction "factory_field_name_clash" FactoryFieldNameClash.
