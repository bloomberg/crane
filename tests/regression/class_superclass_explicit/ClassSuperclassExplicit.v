(* WIP: explicit superclass projection application; the generated C++ does not compile. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ClassSuperclassExplicit.
Class Base (A : Type) := { base : A -> nat }.
Class Ext (A : Type) := { ext_base : Base A ; ext : A -> nat }.
Instance bn : Base nat := { base := fun n => n }.
Instance en : Ext nat := { ext_base := bn ; ext := fun n => n + 1 }.
Definition use (A : Type) (E : Ext A) (x : A) : nat := @base A (@ext_base A E) x + ext x.
Definition go : nat := use nat en 3.
End ClassSuperclassExplicit.
Crane Extraction "class_superclass_explicit" ClassSuperclassExplicit.
