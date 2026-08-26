(* WIP: a typeclass with a superclass field: the superclass projection is not emitted correctly and the generated C++ does not compile. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ClassSuperclassField.
Class Eqb (A : Type) := { eqb : A -> A -> bool }.
Class Ord (A : Type) := { ord_eq :: Eqb A ; le : A -> A -> bool }.
Instance eqnat : Eqb nat := { eqb := Nat.eqb }.
Instance ordnat : Ord nat := { ord_eq := eqnat ; le := Nat.leb }.
Definition cmp (A : Type) (O : Ord A) (x y : A) : nat :=
  if eqb x y then 0 else if le x y then 1 else 2.
Definition go : nat := cmp nat ordnat 1 2.
End ClassSuperclassField.
Crane Extraction "class_superclass_field" ClassSuperclassField.
