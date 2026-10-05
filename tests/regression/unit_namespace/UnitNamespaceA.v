(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.
From Corelib Require Import Datatypes.

(** One of two independently extracted units that both use [list]: each
    defines it, so each is extracted into a namespace of its own. *)
Module UnitNamespaceA.

Fixpoint sum (l : list nat) : nat :=
  match l with nil => 0 | cons x xs => x + sum xs end.

Definition sample : list nat := cons 1 (cons 2 (cons 3 nil)).

End UnitNamespaceA.

Set Crane Unit Namespace.
Crane Extraction "unit_namespace_a" UnitNamespaceA.
