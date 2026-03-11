(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: explicit type applications with instance arguments should reduce cleanly. *)

From Stdlib Require Import Nat.

Module TodoTypeAppInstanceAlias.

Class Boxed (A : Type) := {
  boxed_default : A
}.

#[global] Instance natBoxed : Boxed nat := {
  boxed_default := 7
}.

Definition pick {A : Type} `{Boxed A} : A :=
  boxed_default.

Definition test_value : nat :=
  let alias := @pick in
  alias nat natBoxed + alias nat natBoxed.

End TodoTypeAppInstanceAlias.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_type_app_instance_alias" TodoTypeAppInstanceAlias.
