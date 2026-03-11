(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: erased proof parameters combined with instances should preserve arity. *)

From Stdlib Require Import Nat.

Module TodoErasedInstanceParam.

Class Default (A : Type) := {
  def : A
}.

#[global] Instance natDefault : Default nat := {
  def := 4
}.

Definition pick {A : Type} `{Default A} (_ : True) : A :=
  def.

Definition test_value : nat :=
  @pick nat natDefault I + @pick nat natDefault I.

End TodoErasedInstanceParam.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "todo_erased_instance_param" TodoErasedInstanceParam.
