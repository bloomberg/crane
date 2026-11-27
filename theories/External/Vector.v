(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Mutable vector effects for the standard library flavor.

    Re-exports shared definitions from [VectorDefs.v] and adds the
    [std::vector] C++ type mapping. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export External.VectorDefs.

From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance vector_mapping (A : Type) : TypeMapping (vector A) :=
  value_type ["vector"] (Apply "std::vector" [TypeArg (SourceType A)]) UnknownCopy.
