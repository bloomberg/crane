(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A module type declared inside another module yields no concept at all: the
    enclosing module is emitted as an empty [struct Defs], and the functor
    constrained by it names a concept that was never declared. *)

Module NestedModuleTypeConcept.

  Module Defs.
    Module Type S.
      Parameter t : Type.
      Parameter d : t.
    End S.
  End Defs.

  Module F (X : Defs.S).
    Definition get : X.t := X.d.
  End F.

  Module A.
    Definition t := nat.
    Definition d : t := 1.
  End A.

  Module FA := F A.

  Definition test : nat := FA.get.

End NestedModuleTypeConcept.

Crane Extraction "nested_module_type_concept" NestedModuleTypeConcept.
