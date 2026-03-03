(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Typeclasses — instance resolution, dictionary passing, *)
(* chained instances, superclasses. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module Typeclasses.

(* === Basic typeclass === *)

Class Numeric (A : Type) := {
  to_nat : A -> nat
}.

(* === Simple instances === *)

Instance numNat : Numeric nat := {
  to_nat := fun n => n
}.

Instance numBool : Numeric bool := {
  to_nat := fun b => if b then 1 else 0
}.

(* === Chained instances (depend on Numeric A) === *)

Instance numOption {A : Type} `{Numeric A} : Numeric (option A) := {
  to_nat := fun o =>
    match o with
    | None => 0
    | Some x => S (to_nat x)
    end
}.

Instance numList {A : Type} `{Numeric A} : Numeric (list A) := {
  to_nat :=
    fix sum (l : list A) : nat :=
      match l with
      | nil => 0
      | cons x rest => to_nat x + sum rest
      end
}.

(* === Polymorphic functions using typeclass constraint === *)

Definition numeric_sum {A : Type} `{Numeric A} (l : list A) : nat :=
  to_nat l.

Definition numeric_double {A : Type} `{Numeric A} (x : A) : nat :=
  to_nat x + to_nat x.

(* === Superclass pattern === *)

Class Eq (A : Type) := {
  eqb : A -> A -> bool
}.

Class Ord (A : Type) `{Eq A} := {
  leb : A -> A -> bool
}.

Instance eqNat : Eq nat := {
  eqb := Nat.eqb
}.

Instance ordNat : Ord nat := {
  leb := Nat.leb
}.

Definition sort_pair {A : Type} `{Ord A} (x y : A) : A * A :=
  if leb x y then (x, y) else (y, x).

Definition min_of {A : Type} `{Ord A} (x y : A) : A :=
  if leb x y then x else y.

Definition max_of {A : Type} `{Ord A} (x y : A) : A :=
  if leb x y then y else x.

(* === Multi-constraint function === *)

Definition describe {A : Type} `{Numeric A} `{Eq A} (x y : A) : nat :=
  if eqb x y then to_nat x else to_nat x + to_nat y.

(* === Test values === *)

Definition test_nat         : nat := to_nat 42.
Definition test_bool_true   : nat := to_nat true.
Definition test_bool_false  : nat := to_nat false.
Definition test_option_some : nat := to_nat (Some 5).
Definition test_option_none : nat := to_nat (@None nat).
Definition test_list        : nat := to_nat [1; 2; 3; 4].
Definition test_sum         : nat := numeric_sum [10; 20; 30].
Definition test_double      : nat := numeric_double 7.
Definition test_sort_pair   : nat * nat := sort_pair 5 3.
Definition test_min         : nat := min_of 8 3.
Definition test_max         : nat := max_of 8 3.
Definition test_describe_eq : nat := describe 5 5.
Definition test_describe_ne : nat := describe 3 7.

End Typeclasses.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "typeclasses" Typeclasses.
