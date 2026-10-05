(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.
From Corelib Require Import Datatypes.

(** The other unit: a different selection of functions over the same
    [list], so a different definition of its C++ type. *)
Module UnitNamespaceB.

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with nil => 0 | cons _ xs => S (length xs) end.

Definition sample : list nat := cons 4 (cons 5 nil).

End UnitNamespaceB.

Set Crane Unit Namespace.
Crane Extraction "unit_namespace_b" UnitNamespaceB.
