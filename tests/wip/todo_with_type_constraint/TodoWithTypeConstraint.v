(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: module type constraints with a fixed type definition. *)

From Stdlib Require Import Nat.

Module TodoWithTypeConstraint.

Module Type BASE.
  Parameter t : Type.
  Parameter zero : t.
  Parameter bump : t -> t.
End BASE.

Module Type NAT_BASE := BASE with Definition t := nat.

Module NatBase <: NAT_BASE.
  Definition t := nat.
  Definition zero := 0.
  Definition bump (n : nat) : nat :=
    S n.
End NatBase.

Module UseNat (X : NAT_BASE).
  Definition twice : nat :=
    X.bump (X.bump X.zero).
End UseNat.

Module Applied := UseNat NatBase.

Definition test_twice : nat :=
  Applied.twice.

End TodoWithTypeConstraint.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_with_type_constraint" TodoWithTypeConstraint.
