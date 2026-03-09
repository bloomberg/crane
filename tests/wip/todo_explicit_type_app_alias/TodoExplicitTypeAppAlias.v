(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: explicit type application through a let-bound alias. *)

From Stdlib Require Import Nat Bool.

Module TodoExplicitTypeAppAlias.

Definition id {A : Type} (x : A) : A := x.

Definition test_value : nat :=
  let alias := @id in
  let kept_nat := alias nat 9 in
  let kept_bool := alias bool true in
  kept_nat + if kept_bool then 1 else 0.

End TodoExplicitTypeAppAlias.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_explicit_type_app_alias" TodoExplicitTypeAppAlias.
