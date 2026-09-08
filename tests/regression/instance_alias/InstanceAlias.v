(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** A constant whose type is a class applied to arguments is treated purely as
    an instance declaration: Crane emits [static_assert(Monoid<dict, ...>)] for
    it but never emits [dict] itself, so every use is an undeclared identifier.
    An instance bound to a record literal (rather than to another instance's
    name) is emitted correctly, so it is the aliasing that is lost. *)

Module InstanceAlias.

  Class Monoid (A : Type) := { zero : A ; op : A -> A -> A }.

  Instance MNat : Monoid nat := { zero := 0 ; op := Nat.add }.

  Definition dict : Monoid nat := MNat.

  Definition test : nat := @op _ dict 3 4.

End InstanceAlias.

Crane Extraction "instance_alias" InstanceAlias.
