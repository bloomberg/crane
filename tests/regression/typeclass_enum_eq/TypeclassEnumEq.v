(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: a typeclass instantiated at a user-defined enumeration, with no *)
(* numeric types anywhere, so the generated concept/instance/constrained *)
(* template can be read without reference to any numeral mapping. *)

Module TypeclassEnumEq.

(** A three-valued enumeration. Every constructor is nullary, so this
    extracts to a C++ [enum class]. *)
Inductive color : Type := red | green | blue.

(** Decidable equality, as a typeclass over an arbitrary carrier. *)
Class Eq (A : Type) : Type :=
  { eqb : A -> A -> bool }.

(** Returns [true] when [x] and [y] are the same colour. *)
Definition color_eqb (x y : color) : bool :=
  match x, y with
  | red, red => true
  | green, green => true
  | blue, blue => true
  | _, _ => false
  end.

#[export] Instance ColorEq : Eq color := { eqb := color_eqb }.

(** Equality at any type with an [Eq] instance. *)
Definition is_equal {A : Type} `{Eq A} (x y : A) : bool := eqb x y.

Definition test_same : bool := is_equal red red.
Definition test_diff : bool := is_equal red blue.

End TypeclassEnumEq.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extraction "typeclass_enum_eq" TypeclassEnumEq.
