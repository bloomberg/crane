(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Test sections, module types with multiple inheritance, and other
   complex module system features that might create unusual patterns.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module SectionsModules.

(* Section with parameters *)
Section WithParams.
  Variable x : nat.
  Variable y : nat.

  Definition add_params (n : nat) : nat := n + x + y.

  Fixpoint count_down_from_x (n : nat) : nat :=
    match n with
    | O => x
    | S n' => count_down_from_x n' + y
    end.
End WithParams.

(* Module type with multiple parents - might create complex signatures *)
Module Type Semigroup.
  Parameter T : Type.
  Parameter op : T -> T -> T.
End Semigroup.

Module Type HasIdentity.
  Parameter T : Type.
  Parameter id : T.
End HasIdentity.

(* Module type including two others *)
Module Type Monoid.
  Parameter T : Type.
  Parameter op : T -> T -> T.
  Parameter id : T.
  Axiom left_id : forall x : T, op id x = x.
  Axiom right_id : forall x : T, op x id = x.
End Monoid.

(* Implementation *)
Module NatMonoid <: Monoid.
  Definition T := nat.
  Definition op := Nat.add.
  Definition id := 0.
  Axiom left_id : forall x : T, op id x = x.
  Axiom right_id : forall x : T, op x id = x.
End NatMonoid.

(* Transparent ascription *)
Module TransparentMod := NatMonoid.

(* Use monoid *)
Definition use_monoid := TransparentMod.op 5 10.

(* Higher-order module - module taking module as parameter *)
Module MakeDoubleOp (M : Semigroup).
  Definition double (x : M.T) : M.T := M.op x x.
  Definition quad (x : M.T) : M.T := double (double x).
End MakeDoubleOp.

Module NatDoubleOp := MakeDoubleOp NatMonoid.
Definition test_double := NatDoubleOp.double 5.

(* Module with local definitions *)
Module LocalDefs.
  #[local] Definition private_helper (n : nat) : nat := n * 2.

  Definition public_use (n : nat) : nat := private_helper n + 1.
End LocalDefs.

(* Nested sections *)
Section Outer.
  Variable a : nat.

  Section Inner.
    Variable b : nat.

    Definition use_both (c : nat) : nat := a + b + c.
  End Inner.

  Definition use_outer (c : nat) : nat := a + c.
End Outer.

(* Module with Include *)
Module Base.
  Definition base_val := 42.
  Definition base_fun (n : nat) : nat := n + 1.
End Base.

Module Extended.
  Include Base.
  Definition extended_val := 100.
  Definition extended_fun (n : nat) : nat := base_fun n + extended_val.
End Extended.

Definition test_extended := Extended.extended_fun Extended.base_val.

End SectionsModules.

Crane Extraction "sections_modules" SectionsModules.
