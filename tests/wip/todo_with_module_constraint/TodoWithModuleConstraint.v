(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: module type constraints with a fixed nested module. *)

From Stdlib Require Import Nat.

Module TodoWithModuleConstraint.

Module Type INNER.
  Parameter t : Type.
  Parameter zero : t.
End INNER.

Module NatInner <: INNER.
  Definition t := nat.
  Definition zero := 0.
End NatInner.

Module Type OUTER.
  Declare Module Inner : INNER.
  Parameter step : Inner.t -> Inner.t.
End OUTER.

Module Type OUTER_NAT := OUTER with Module Inner := NatInner.

Module NatOuter <: OUTER_NAT.
  Module Inner := NatInner.
  Definition step (n : Inner.t) : Inner.t :=
    S n.
End NatOuter.

Module UseNat (X : OUTER_NAT).
  Definition twice : nat :=
    X.step (X.step X.Inner.zero).
End UseNat.

Module Applied := UseNat NatOuter.

Definition test_twice : nat :=
  Applied.twice.

End TodoWithModuleConstraint.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_with_module_constraint" TodoWithModuleConstraint.
