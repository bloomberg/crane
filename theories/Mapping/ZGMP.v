(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [Z] (binary integers) to GMP [mpz_class].

    Builds on [NGMP.v] which already extracts [positive] and [N].
    Maps [Z] to [mpz_class] with GMP arbitrary-precision arithmetic.

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)
From Crane Require Extraction.
From Crane Require Export Mapping.NGMP Mapping.NatGMP.
From Stdlib Require Import BinInt.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** [Z] is a GMP [mpz_class]; a numeral is gmpxx's exact literal [(n_mpz)]. *)
#[export] Instance gmp_z_mapping : TypeMapping Z :=
  {| type_headers := ["gmpxx.h"];
     type_cpp := Crane.Cpp.Name "mpz_class";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews Z;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Z0;
             ctor_build := Expr "mpz_class(0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 0";
                       case_fields := [] |} |};
          {| ctor_source := Ref Zpos;
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut > 0";
                       case_fields := [(0, OwnedProjection "%scrut")] |} |};
          {| ctor_source := Ref Zneg;
             ctor_build := Expr "(-%a0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut < 0";
                       case_fields := [(0, OwnedProjection "-%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref Z0; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref Zpos; numeral_action := NumeralIdentity 0 |};
                  {| numeral_constructor := Ref Zneg; numeral_action := NumeralNegate 0 |}];
               numeral_emitter := IntegerToken "(" "_mpz)";
               numeral_converters := [Ref Z.of_num_int; Ref Z.of_num_uint] |} |}.

(* Z operations *)
(** [Z.add] is exact [mpz_class] [+]. *)
#[export] Instance gmp_z_add_mapping : OperationMapping (Ref Z.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.sub] is exact [mpz_class] [-]. *)
#[export] Instance gmp_z_sub_mapping : OperationMapping (Ref Z.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(m) - %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "m"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.mul] is exact [mpz_class] [*]. *)
#[export] Instance gmp_z_mul_mapping : OperationMapping (Ref Z.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.div] and [Z.modulo] floor (the remainder takes the divisor's sign),
    whereas GMP's [/] and [%] truncate toward zero: the truncated result is
    corrected for operands of opposite sign.  A zero divisor follows Rocq
    ([a / 0 = 0], [a mod 0 = a]). *)
#[export] Instance gmp_z_div_mapping : OperationMapping (Ref Z.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "[](mpz_class _a, mpz_class _b) -> mpz_class {
  if (_b == 0) return mpz_class(0);
  mpz_class _q = _a / _b;
  mpz_class _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _q - 1;
  return _q;
}(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.modulo]: the floored remainder, as for [gmp_z_div_mapping]. *)
#[export] Instance gmp_z_modulo_mapping : OperationMapping (Ref Z.modulo) :=
  {| operation_headers := [];
     operation_cpp := Expr "[](mpz_class _a, mpz_class _b) -> mpz_class {
  if (_b == 0) return _a;
  mpz_class _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _r + _b;
  return _r;
}(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.opp] is exact negation. *)
#[export] Instance gmp_z_opp_mapping : OperationMapping (Ref Z.opp) :=
  {| operation_headers := [];
     operation_cpp := Expr "(-%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.abs] is gmpxx's [abs]. *)
#[export] Instance gmp_z_abs_mapping : OperationMapping (Ref Z.abs) :=
  {| operation_headers := [];
     operation_cpp := Expr "abs(%arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.succ] is [x + 1]. *)
#[export] Instance gmp_z_succ_mapping : OperationMapping (Ref Z.succ) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.pred] is [x - 1]. *)
#[export] Instance gmp_z_pred_mapping : OperationMapping (Ref Z.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) - 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.eqb] is [==]. *)
#[export] Instance gmp_z_eqb_mapping : OperationMapping (Ref Z.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.ltb] is [<]. *)
#[export] Instance gmp_z_ltb_mapping : OperationMapping (Ref Z.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.leb] is [<=]. *)
#[export] Instance gmp_z_leb_mapping : OperationMapping (Ref Z.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.gtb] is [>]. *)
#[export] Instance gmp_z_gtb_mapping : OperationMapping (Ref Z.gtb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) > %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.geb] is [>=]. *)
#[export] Instance gmp_z_geb_mapping : OperationMapping (Ref Z.geb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) >= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.compare] is two [<] tests yielding [Lt], [Gt] or [Eq]. *)
#[export] Instance gmp_z_compare_mapping : OperationMapping (Ref Z.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) < %arg(y) ? %ret::LT : (%arg(y) < %arg(x) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.eq_dec] is [==]: the [sumbool] is a [bool]. *)
#[export] Instance gmp_z_eq_dec_mapping : OperationMapping (Ref Z.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.min] is a [<=] conditional. *)
#[export] Instance gmp_z_min_mapping : OperationMapping (Ref Z.min) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) <= %arg(m) ? %arg(n) : %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.max] is a [>=] conditional. *)
#[export] Instance gmp_z_max_mapping : OperationMapping (Ref Z.max) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) >= %arg(m) ? %arg(n) : %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.

(* Conversions *)
(** [Z.of_nat] constructs an [mpz_class] from the [nat], exactly. *)
#[export] Instance gmp_z_of_nat_mapping : OperationMapping (Ref Z.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "mpz_class(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.to_nat] sends negatives to [0] and saturates at [UINT_MAX]:
    [mpz_class::get_ui] keeps only the low word, and a silently wrapped
    result would be wrong (CWE-190/CWE-681). *)
#[export] Instance gmp_z_to_nat_mapping : OperationMapping (Ref Z.to_nat) :=
  {| operation_headers := ["climits"];
     operation_cpp := Expr "(%arg(z) < 0 ? 0 : (%arg(z) > mpz_class(UINT_MAX) ? UINT_MAX : static_cast<unsigned int>(%arg(z).get_ui())))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.of_N] is the same [mpz_class]. *)
#[export] Instance gmp_z_of_N_mapping : OperationMapping (Ref Z.of_N) :=
  {| operation_headers := [];
     operation_cpp := Expr "mpz_class(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.to_N] sends negatives to [0]; exact otherwise. *)
#[export] Instance gmp_z_to_N_mapping : OperationMapping (Ref Z.to_N) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(z) < 0 ? mpz_class(0) : %arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.abs_N] is gmpxx's [abs]. *)
#[export] Instance gmp_z_abs_N_mapping : OperationMapping (Ref Z.abs_N) :=
  {| operation_headers := [];
     operation_cpp := Expr "abs(%arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
