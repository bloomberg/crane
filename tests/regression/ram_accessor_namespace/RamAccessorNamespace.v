(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: namespace-sensitive constructor escaping pressure *)

From Stdlib Require Import Nat.

Module RamAccessorNamespace.

Inductive item : Type := S' | S_.

Definition score (x : item) : nat :=
  match x with
  | S' => 1
  | S_ => 2
  end.

Definition t : nat := score S' + score S_.
End RamAccessorNamespace.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_accessor_namespace" RamAccessorNamespace.