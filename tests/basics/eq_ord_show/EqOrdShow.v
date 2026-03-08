(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std NatIntStd.
From Corelib Require Import PrimString.

(* ============================================================= *)
(* Type Classes *)
(* ============================================================= *)

(* Simple equality type class *)
Class Eq (A : Type) : Type :=
  { eqb : A -> A -> bool
  ; neqb : A -> A -> bool
  }.

(* Ordering type class - requires Eq *)
Class Ord (A : Type) `{Eq A} : Type :=
  { lt : A -> A -> bool
  ; le : A -> A -> bool
  ; gt : A -> A -> bool
  ; ge : A -> A -> bool
  }.

(* Show type class - convert to string *)
Class Show (A : Type) : Type :=
  { show : A -> string
  }.

(* ============================================================= *)
(* Instances for nat *)
(* ============================================================= *)

#[export] Instance NatEq : Eq nat := {
  eqb := Nat.eqb;
  neqb := fun x y => negb (Nat.eqb x y)
}.

#[export] Instance NatOrd : Ord nat := {
  lt := Nat.ltb;
  le := Nat.leb;
  gt := fun x y => Nat.ltb y x;
  ge := fun x y => Nat.leb y x
}.

#[export] Instance NatShow : Show nat := {
  show := fun _ => "<nat>"%pstring
}.

(* ============================================================= *)
(* Functions using Type Classes *)
(* ============================================================= *)

(* Function using Eq *)
Definition is_equal {A : Type} `{Eq A} (x y : A) : bool :=
  eqb x y.

(* Function using Eq *)
Definition is_different {A : Type} `{Eq A} (x y : A) : bool :=
  neqb x y.

(* Function using Ord *)
Definition is_less_than {A : Type} `{Ord A} (x y : A) : bool :=
  lt x y.

(* Function using Ord *)
Definition is_less_or_equal {A : Type} `{Ord A} (x y : A) : bool :=
  le x y.

(* Simple comparison result type *)
Inductive Ordering : Type :=
  | LT : Ordering
  | EQ : Ordering
  | GT : Ordering.

(* Function combining Ord comparisons *)
Definition compare {A : Type} `{Ord A} (x y : A) : Ordering :=
  if lt x y then LT
  else if eqb x y then EQ
  else GT.

(* Function using Show *)
Definition to_string {A : Type} `{Show A} (x : A) : string :=
  show x.

(* Function using multiple type classes: Eq and Show *)
Definition show_if_equal {A : Type} `{Eq A} `{Show A} (x y : A) : string :=
  if eqb x y then show x else "not equal"%pstring.

(* Function using Ord and Show *)
Definition show_comparison {A : Type} `{Ord A} `{Show A} (x y : A) : string :=
  if lt x y then cat (cat (show x) " < "%pstring) (show y)
  else if eqb x y then cat (cat (show x) " = "%pstring) (show y)
  else cat (cat (show x) " > "%pstring) (show y).

(* ============================================================= *)
(* Test Values *)
(* ============================================================= *)

(* Test is_equal *)
Definition test_eq_true : bool := is_equal (A := nat) 42 42.
Definition test_eq_false : bool := is_equal (A := nat) 42 43.

(* Test is_different *)
Definition test_neq_true : bool := is_different (A := nat) 42 43.
Definition test_neq_false : bool := is_different (A := nat) 42 42.

(* Test is_less_than *)
Definition test_lt_true : bool := is_less_than (A := nat) 10 20.
Definition test_lt_false : bool := is_less_than (A := nat) 20 10.

(* Test compare *)
Definition test_compare_lt : Ordering := compare (A := nat) 10 20.
Definition test_compare_eq : Ordering := compare (A := nat) 15 15.
Definition test_compare_gt : Ordering := compare (A := nat) 20 10.

(* Test to_string *)
Definition test_show : string := to_string (A := nat) 42.

(* Extract everything *)
Crane Extraction "eq_ord_show"
  Eq NatEq
  Ord NatOrd
  Show NatShow
  Ordering
  is_equal is_different is_less_than is_less_or_equal
  compare to_string show_if_equal show_comparison
  test_eq_true test_eq_false
  test_neq_true test_neq_false
  test_lt_true test_lt_false
  test_compare_lt test_compare_eq test_compare_gt
  test_show.
