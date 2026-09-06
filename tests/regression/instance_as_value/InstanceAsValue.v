(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A typeclass dictionary bound to a name, built by a function, and a class
    method partially applied to one.  Each treats the instance as a value; the
    plugin raises an anomaly instead of extracting it. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
Require Import List.
Import ListNotations.

Module InstanceAsValue.
Class Monoid (A : Type) := { unit_ : A ; op : A -> A -> A }.
Instance MNat : Monoid nat := { unit_ := 0 ; op := Nat.add }.
Definition dict : Monoid nat := MNat.
Definition mkDict (base : nat) : Monoid nat := {| unit_ := base ; op := Nat.add |}.
Definition mconcat {A} (M : Monoid A) (l : list A) : A := fold_right (@op A M) (@unit_ A M) l.
Definition method : nat -> nat -> nat := @op nat MNat.
Definition run : nat :=
  mconcat dict [1;2] + mconcat (mkDict 10) [1] + method 3 4.
End InstanceAsValue.

Crane Extraction "instance_as_value" InstanceAsValue.run.
