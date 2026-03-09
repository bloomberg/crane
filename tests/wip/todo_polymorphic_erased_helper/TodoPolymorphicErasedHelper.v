(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: local polymorphic helpers with erased proof arguments. *)

From Stdlib Require Import Nat Bool.

Module TodoPolymorphicErasedHelper.

Definition test_value : nat :=
  let aux {A : Type} (x : A) (_ : True) : A := x in
  let kept_nat := aux 7 I in
  let kept_bool := aux true I in
  kept_nat + if kept_bool then 1 else 0.

End TodoPolymorphicErasedHelper.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_polymorphic_erased_helper" TodoPolymorphicErasedHelper.
