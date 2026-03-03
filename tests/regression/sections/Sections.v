(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test Rocq sections *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module Sections.

(* Section with a variable *)
Section WithNat.
  Variable n : nat.

  Definition add_n (m : nat) : nat := Nat.add n m.
  Definition mul_n (m : nat) : nat := Nat.mul n m.
End WithNat.

(* After section, n becomes a parameter *)
Definition add_five := add_n five.
Definition mul_three := mul_n three.

(* Nested sections *)
Section Outer.
  Variable a : nat.

  Section Inner.
    Variable b : nat.

    Definition sum_ab : nat := Nat.add a b.
    Definition prod_ab : nat := Nat.mul a b.
  End Inner.

  (* b is now a parameter, a is still in scope *)
  Definition use_inner := sum_ab three.
End Outer.

(* Both a and b are now parameters *)
Definition final_use := use_inner five.

(* Section with type variable *)
Section Polymorphic.
  Variable A : Type.

  Definition identity (x : A) : A := x.
  Definition const (x y : A) : A := x.
End Polymorphic.

(* Test values *)
Definition test_add := add_five two.
Definition test_mul := mul_three four.
Definition test_nested := final_use.
Definition test_id := identity nat seven.
Definition test_const := const nat three nine.

End Sections.

Crane Extraction "sections" Sections.
