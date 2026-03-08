(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: nested module requirements inside module types. *)

From Stdlib Require Import Nat.

Module TodoNestedModuleType.

Module Type INNER.
  Parameter t : Type.
  Parameter zero : t.
End INNER.

Module Type OUTER.
  Declare Module Inner : INNER.
  Parameter step : Inner.t -> Inner.t.
End OUTER.

Module Make (X : OUTER).
  Definition twice : X.Inner.t :=
    X.step (X.step X.Inner.zero).
End Make.

Module NatInner <: INNER.
  Definition t := nat.
  Definition zero := 0.
End NatInner.

Module NatOuter <: OUTER.
  Module Inner := NatInner.
  Definition step (n : Inner.t) : Inner.t :=
    S n.
End NatOuter.

Module UseNat := Make NatOuter.

Definition test_twice : nat :=
  UseNat.twice.

End TodoNestedModuleType.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_nested_module_type" TodoNestedModuleType.
