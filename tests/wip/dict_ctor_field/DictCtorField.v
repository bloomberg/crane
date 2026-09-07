(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A type class becomes a C++ concept, so a constructor field whose Rocq type
    is a class applied to a concrete type has no C++ type to be given.  Crane
    writes the concept's name where a type belongs, producing
    [Sz a0;] as a data member and passing the instance [SzNat] as a value. *)

Module DictCtorField.

  Class Sz (A : Type) := { sz : A -> nat }.

  Instance SzNat : Sz nat := { sz := fun n => n }.

  Inductive box := Box : Sz nat -> nat -> box.

  Definition run (b : box) : nat := match b with Box d n => @sz nat d n end.

  Definition test : nat := run (Box SzNat 7).

End DictCtorField.

Crane Extraction "dict_ctor_field" DictCtorField.
