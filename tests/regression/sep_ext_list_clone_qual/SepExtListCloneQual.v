(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: the iterative clone() loop body for an inductive type
   that has a `list<Self>` field must use the fully-qualified type name
   `Datatypes::List<T>`, not the bare `List<T>`.  Previously the loop
   used Tid_external which bypasses qualify_inductives, producing
   unqualified references that fail to compile. *)

From Stdlib Require Import List.

Inductive Forest (A : Type) : Type :=
  | Leaf : Forest A
  | Node : A -> list (Forest A) -> Forest A.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Crane Separate Extraction Forest.
