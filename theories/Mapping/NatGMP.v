(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [nat] to GMP's [mpz_class] (arbitrary-precision integers).

    This maps Peano-style [nat] to the C++ wrapper [mpz_class] from
    [<gmpxx.h>], providing unlimited precision arithmetic.

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** [nat] is a GMP [mpz_class]; a numeral is gmpxx's exact literal [(n_mpz)]. *)
#[export] Instance gmp_nat_mapping : TypeMapping nat :=
  {| type_headers := ["gmpxx.h"];
     type_cpp := Crane.Cpp.Name "mpz_class";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews nat;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref O;
             ctor_build := Expr "mpz_class(0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut <= 0";
                       case_fields := [] |} |};
          {| ctor_source := Ref S;
             ctor_build := Expr "(mpz_class(%a0) + 1)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut > 0";
                       case_fields := [(0, OwnedProjection "%scrut - 1")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref O; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref S; numeral_action := NumeralSuccessor 0 |}];
               numeral_emitter := IntegerToken "(" "_mpz)";
               numeral_converters := [Ref Nat.of_num_uint] |} |}.

(** [Nat.add] is exact [mpz_class] [+]. *)
#[export] Instance gmp_nat_add_mapping : OperationMapping (Ref Nat.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.mul] is exact [mpz_class] [*]. *)
#[export] Instance gmp_nat_mul_mapping : OperationMapping (Ref Nat.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) * %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.div] is GMP [/], with Rocq's [x / 0 = 0]. *)
#[export] Instance gmp_nat_div_mapping : OperationMapping (Ref Nat.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) ? %arg(x) / %arg(y) : mpz_class(0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.modulo] is GMP [%], with Rocq's [x mod 0 = x]. *)
#[export] Instance gmp_nat_modulo_mapping : OperationMapping (Ref Nat.modulo) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) ? %arg(x) % %arg(y) : %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.double] is [n + n]. *)
#[export] Instance gmp_nat_double_mapping : OperationMapping (Ref Nat.double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.pred] is [n - 1], keeping [pred 0 = 0]. *)
#[export] Instance gmp_nat_pred_mapping : OperationMapping (Ref Nat.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) > 0 ? %arg(n) - 1 : %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.sub] truncates at [0] so the result never goes negative. *)
#[export] Instance gmp_nat_sub_mapping : OperationMapping (Ref Nat.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) >= %arg(m) ? %arg(n) - %arg(m) : mpz_class(0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.max] is a [>=] conditional. *)
#[export] Instance gmp_nat_max_mapping : OperationMapping (Ref Nat.max) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) >= %arg(m) ? %arg(n) : %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.min] is a [<=] conditional. *)
#[export] Instance gmp_nat_min_mapping : OperationMapping (Ref Nat.min) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) <= %arg(m) ? %arg(n) : %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.eqb] is [==]. *)
#[export] Instance gmp_nat_eqb_mapping : OperationMapping (Ref Nat.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.ltb] is [<]. *)
#[export] Instance gmp_nat_ltb_mapping : OperationMapping (Ref Nat.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) < %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.leb] is [<=]. *)
#[export] Instance gmp_nat_leb_mapping : OperationMapping (Ref Nat.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) <= %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Nat.compare] is two [<] tests yielding [Lt], [Gt] or [Eq]. *)
#[export] Instance gmp_nat_compare_mapping : OperationMapping (Ref Nat.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) < %arg(m) ? %ret::LT : (%arg(m) < %arg(n) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.

(* [PeanoNat.Nat] includes [Nat]: its [add], [mul], ... are the same
   constants, mapped above; only [eq_dec] is its own. *)
From Stdlib Require PeanoNat.

(** [PeanoNat.Nat.eq_dec] is [==]: the [sumbool] is a [bool]. *)
#[export] Instance gmp_peano_nat_eq_dec_mapping : OperationMapping (Ref PeanoNat.Nat.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.

From Corelib Require Import PrimInt63.
(** Reads a primitive [int] as a [nat]; realised in C++ only. *)
Axiom nat_of_int : int -> nat.
(** [nat_of_int] constructs an [mpz_class], exactly. *)
#[export] Instance gmp_nat_of_int_mapping : OperationMapping (Ref nat_of_int) :=
  {| operation_headers := [];
     operation_cpp := Expr "mpz_class(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

From Corelib Require Import PrimString.
(** Decimal rendering of a [nat]; realised in C++ only. *)
Axiom string_of_nat : nat -> string.
(** [string_of_nat] is [mpz_class::get_str], base 10. *)
#[export] Instance gmp_string_of_nat_mapping : OperationMapping (Ref string_of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x).get_str()";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
