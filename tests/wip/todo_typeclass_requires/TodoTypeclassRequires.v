(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* WIP: TODO from src/translation.ml line 11066:
   "Requires clause for typeclass constraints not yet implemented."

   When a function takes a typeclass parameter (e.g. `{Numeric A}`), the
   generated C++ template should have a `requires Numeric<I, T>` constraint
   so that the template can only be instantiated with valid typeclass instances.
   Currently the template parameter _tcI0 is unconstrained, which means any
   struct can be passed even if it doesn't implement the typeclass.

   Expected generated C++:
     template <typename _tcI0, typename T1>
       requires Numeric<_tcI0, T1>   // <-- THIS IS MISSING
     static unsigned int double_val(const T1 &x) { ... }

   Actual generated C++:
     template <typename _tcI0, typename T1>
     static unsigned int double_val(const T1 &x) { ... }

   The test currently PASSES because the code compiles and runs correctly even
   without the requires clause. It serves as a regression test for when the
   requires clause is eventually implemented. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module TodoTypeclassRequires.

  Class Numeric (A : Type) := {
    to_nat_val : A -> nat
  }.

  #[export] Instance NatNumeric : Numeric nat := {
    to_nat_val := fun n => n
  }.

  (* This function takes a typeclass parameter. The generated C++ template
     should have `requires Numeric<_tcI0, T1>` but currently doesn't. *)
  Definition double_val {A : Type} `{Numeric A} (x : A) : nat :=
    to_nat_val x + to_nat_val x.

  Definition test_result : nat := double_val (H := NatNumeric) 7.

End TodoTypeclassRequires.

Crane Extraction "todo_typeclass_requires" TodoTypeclassRequires.
