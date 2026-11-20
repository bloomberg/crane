(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Stdlib Require Import BinNat BinPos.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** Extraction of [N] (binary natural numbers) to GMP [mpz_class].

    Maps [positive] and [N] to [mpz_class] from [<gmpxx.h>].

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)

(** [positive] and [N] are GMP [mpz_class]es; a numeral is gmpxx's exact literal [(n_mpz)]. *)
#[export] Instance gmp_positive_mapping : TypeMapping positive :=
  {| type_headers := ["gmpxx.h"];
     type_cpp := Crane.Cpp.Name "mpz_class";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews positive;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref xH;
             ctor_build := Expr "mpz_class(1)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 1";
                       case_fields := [] |} |};
          {| ctor_source := Ref xI;
             ctor_build := Expr "(2 * %a0 + 1)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut % 2 != 0";
                       case_fields := [(0, OwnedProjection "(%scrut - 1) / 2")] |} |};
          {| ctor_source := Ref xO;
             ctor_build := Expr "(2 * %a0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut % 2 == 0";
                       case_fields := [(0, OwnedProjection "%scrut / 2")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref xI; numeral_action := NumeralDoublePlusOne 0 |};
                  {| numeral_constructor := Ref xO; numeral_action := NumeralDouble 0 |};
                  {| numeral_constructor := Ref xH; numeral_action := NumeralOne |}];
               numeral_emitter := IntegerToken "(" "_mpz)";
               numeral_converters := [] |} |}.

#[export] Instance gmp_n_mapping : TypeMapping N :=
  {| type_headers := ["gmpxx.h"];
     type_cpp := Crane.Cpp.Name "mpz_class";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews N;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref N0;
             ctor_build := Expr "mpz_class(0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 0";
                       case_fields := [] |} |};
          {| ctor_source := Ref Npos;
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut != 0";
                       case_fields := [(0, OwnedProjection "%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref N0; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref Npos; numeral_action := NumeralIdentity 0 |}];
               numeral_emitter := IntegerToken "(" "_mpz)";
               numeral_converters := [Ref N.of_num_uint] |} |}.

(* Pos operations *)
#[export] Instance gmp_pos_add_mapping : OperationMapping (Ref Pos.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(* [positive] is strictly >= 1. Rocq's [Pos.sub] truncates at 1 (it returns 1
   when a <= b) and [Pos.pred 1 = 1], keeping the result inside the positive
   domain. Raw subtraction would produce 0 or negative values that violate the
   invariant (CWE-682). *)
#[export] Instance gmp_pos_sub_mapping : OperationMapping (Ref Pos.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) > %arg(y) ? %arg(x) - %arg(y) : mpz_class(1))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_mul_mapping : OperationMapping (Ref Pos.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_succ_mapping : OperationMapping (Ref Pos.succ) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_pred_mapping : OperationMapping (Ref Pos.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) > 1 ? %arg(x) - 1 : mpz_class(1))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_eqb_mapping : OperationMapping (Ref Pos.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(p) == %arg(q)";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "q"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_ltb_mapping : OperationMapping (Ref Pos.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_leb_mapping : OperationMapping (Ref Pos.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_compare_mapping : OperationMapping (Ref Pos.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) < %arg(y) ? %ret::LT : (%arg(y) < %arg(x) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_eq_dec_mapping : OperationMapping (Ref Pos.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_min_mapping : OperationMapping (Ref Pos.min) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(p) <= %arg(p') ? %arg(p) : %arg(p'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "p'"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_max_mapping : OperationMapping (Ref Pos.max) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(p) >= %arg(p') ? %arg(p) : %arg(p'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "p'"; argument_use := Read |}]
         ReturnValue [] |}.

(* N operations *)
#[export] Instance gmp_n_add_mapping : OperationMapping (Ref N.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_sub_mapping : OperationMapping (Ref N.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) >= %arg(m) ? %arg(n) - %arg(m) : mpz_class(0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_mul_mapping : OperationMapping (Ref N.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) * %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_div_mapping : OperationMapping (Ref N.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b) == 0 ? mpz_class(0) : %arg(a) / %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_modulo_mapping : OperationMapping (Ref N.modulo) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b) == 0 ? %arg(a) : %arg(a) % %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_succ_mapping : OperationMapping (Ref N.succ) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_pred_mapping : OperationMapping (Ref N.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) == 0 ? mpz_class(0) : %arg(n) - 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_eqb_mapping : OperationMapping (Ref N.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_ltb_mapping : OperationMapping (Ref N.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_leb_mapping : OperationMapping (Ref N.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_compare_mapping : OperationMapping (Ref N.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) < %arg(m) ? %ret::LT : (%arg(m) < %arg(n) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_eq_dec_mapping : OperationMapping (Ref N.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_min_mapping : OperationMapping (Ref N.min) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) <= %arg(n') ? %arg(n) : %arg(n'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "n'"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_max_mapping : OperationMapping (Ref N.max) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) >= %arg(n') ? %arg(n) : %arg(n'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "n'"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_double_mapping : OperationMapping (Ref N.double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) * 2)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_n_succ_double_mapping : OperationMapping (Ref N.succ_double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * 2 + 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* Conversions *)
#[export] Instance gmp_n_of_nat_mapping : OperationMapping (Ref N.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "mpz_class(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(* [mpz_class::get_ui] returns only the low word of an arbitrary-precision
   value, and Rocq's [N.to_nat]/[Pos.to_nat] are total, unbounded-domain
   functions. Silently truncating a value that exceeds [UINT_MAX] would
   produce a wrapped, wrong result rather than surfacing the loss of
   precision (CWE-190/CWE-681), so we saturate at [UINT_MAX] instead. *)
#[export] Instance gmp_n_to_nat_mapping : OperationMapping (Ref N.to_nat) :=
  {| operation_headers := ["climits"];
     operation_cpp := Expr "(%arg(a) > mpz_class(UINT_MAX) ? UINT_MAX : static_cast<unsigned int>(%arg(a).get_ui()))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_of_nat_mapping : OperationMapping (Ref Pos.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "mpz_class(%arg(n) == 0 ? 1 : %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance gmp_pos_to_nat_mapping : OperationMapping (Ref Pos.to_nat) :=
  {| operation_headers := ["climits"];
     operation_cpp := Expr "(%arg(x) > mpz_class(UINT_MAX) ? UINT_MAX : static_cast<unsigned int>(%arg(x).get_ui()))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
