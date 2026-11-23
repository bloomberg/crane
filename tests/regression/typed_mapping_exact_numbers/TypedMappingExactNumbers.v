(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An exact mapping of [nat] (docs/typed-mappings-design.md 16): a test
    of the descriptors, not a default.  [ExactNat] maps [nat] to
    [boost::multiprecision::cpp_int], so no value wraps:
    - [O] is [cpp_int{0}], [S n] is [n + 1], a match tests [n > 0] and owns
      the predecessor [n - 1] ([OwnedProjection]);
    - a numeral is a decimal string passed to [cpp_int]'s constructor
      ([DecimalConstructor]), so [big], larger than any 64-bit integer, is
      written exactly;
    - [cpp_int] duplicates its digits on copy ([DuplicateValue]), so a
      read-only parameter is passed by [const cpp_int&];
    - [Nat.add], [Nat.mul], [Nat.ltb] read their arguments, and the result
      of an arithmetic operation is converted to [cpp_int] at once, so no
      Boost expression template outlives its operands. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Std Mapping.Descriptor.
Local Open Scope pstring_scope.

Module ExactNat.

  #[export] Instance exact_nat_mapping : TypeMapping nat :=
    {| type_headers := ["boost/multiprecision/cpp_int.hpp"];
       type_cpp := Crane.Cpp.Name "boost::multiprecision::cpp_int";
       type_components := [];
       type_copy := DuplicateValue;
       type_access := ReadOnlyValue ReadByConstReference;
       type_views := NoViews nat;
       type_interface :=
         AlgebraicInterface
           [{| ctor_source := Ref O;
               ctor_build := Expr "boost::multiprecision::cpp_int{0}";
               ctor_view :=
                 Some {| view_requirement := PreferredObservation;
                         case_test := "%scrut == 0";
                         case_fields := [] |} |};
            {| ctor_source := Ref S;
               ctor_build := Expr "boost::multiprecision::cpp_int(%a0 + 1)";
               ctor_view :=
                 Some {| view_requirement := PreferredObservation;
                         case_test := "%scrut > 0";
                         case_fields :=
                           [(0, OwnedProjection "boost::multiprecision::cpp_int(%scrut - 1)")] |} |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals :=
         Some {| numeral_cases :=
                   [{| numeral_constructor := Ref O; numeral_action := NumeralZero |};
                    {| numeral_constructor := Ref S; numeral_action := NumeralSuccessor 0 |}];
                 numeral_emitter := DecimalConstructor "boost::multiprecision::cpp_int";
                 numeral_converters := [Ref Nat.of_num_uint] |} |}.

  #[export] Instance exact_add_mapping : OperationMapping (Ref Nat.add) :=
    {| operation_headers := ["boost/multiprecision/cpp_int.hpp"];
       operation_cpp := Expr "boost::multiprecision::cpp_int(%arg(n) + %arg(m))";
       operation_contract :=
         PureOperation
           [{| argument_name := "n"; argument_use := Read |};
            {| argument_name := "m"; argument_use := Read |}]
           ReturnValue [] |}.

  #[export] Instance exact_mul_mapping : OperationMapping (Ref Nat.mul) :=
    {| operation_headers := ["boost/multiprecision/cpp_int.hpp"];
       operation_cpp := Expr "boost::multiprecision::cpp_int(%arg(n) * %arg(m))";
       operation_contract :=
         PureOperation
           [{| argument_name := "n"; argument_use := Read |};
            {| argument_name := "m"; argument_use := Read |}]
           ReturnValue [] |}.

  #[export] Instance exact_ltb_mapping : OperationMapping (Ref Nat.ltb) :=
    {| operation_headers := [];
       operation_cpp := Expr "(%arg(n) < %arg(m))";
       operation_contract :=
         PureOperation
           [{| argument_name := "n"; argument_use := Read |};
            {| argument_name := "m"; argument_use := Read |}]
           ReturnValue [] |}.

End ExactNat.

Import ExactNat.

Module TypedMappingExactNumbers.

  Fixpoint factorial (n : nat) : nat :=
    match n with
    | 0 => 1
    | S k => n * factorial k
    end.

  (** Larger than [2^64]. *)
  Definition big : nat := 100000000000000000000.

  Definition exceeds_big (n : nat) : bool := Nat.ltb big n.

  Definition predecessor (n : nat) : nat :=
    match n with
    | 0 => 0
    | S k => k
    end.

  Definition sum3 (a b c : nat) : nat := a + b + c.

End TypedMappingExactNumbers.

Crane Extraction "typed_mapping_exact_numbers" TypedMappingExactNumbers.
