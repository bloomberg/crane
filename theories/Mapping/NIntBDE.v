(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.BDE.
From Stdlib Require Import BinNat BinPos.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** Extraction of [N] (binary natural numbers) to [unsigned int].

    Maps [positive] to [unsigned int] and [N] to [unsigned int].
    All [N] and [Pos] operations become native C++ arithmetic.

    WARNING (prototyping only): [unsigned int] is fixed-width, whereas Rocq's
    [positive] and [N] are unbounded. Addition, multiplication, successor,
    doubling, and numeral extraction wrap modulo 2^32 once a value exceeds
    [UINT_MAX], and conversions truncate — silently diverging from the proof
    model (CWE-190/CWE-681). Use this mapping only for testing/prototyping where
    values are provably in range; for security-sensitive or unbounded arithmetic
    use the arbitrary-precision GMP mappings ([Mapping.NGMP], [Mapping.ZGMP])
    instead.
*)

(** [positive] is an [unsigned int]: [xI p] is [2p + 1], [xO p] is [2p],
    [xH] is [1]; a match tests [1], then oddness; a numeral is an
    [unsigned int] literal. *)
#[export] Instance bde_positive_mapping : TypeMapping positive :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "unsigned int";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews positive;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref xH;
             ctor_build := Expr "1u";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 1u";
                       case_fields := [] |} |};
          {| ctor_source := Ref xI;
             ctor_build := Expr "(2u * %a0 + 1u)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut % 2u != 0u";
                       case_fields := [(0, OwnedProjection "(%scrut - 1u) / 2u")] |} |};
          {| ctor_source := Ref xO;
             ctor_build := Expr "(2u * %a0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut % 2u == 0u";
                       case_fields := [(0, OwnedProjection "%scrut / 2u")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref xI; numeral_action := NumeralDoublePlusOne 0 |};
                  {| numeral_constructor := Ref xO; numeral_action := NumeralDouble 0 |};
                  {| numeral_constructor := Ref xH; numeral_action := NumeralOne |}];
               numeral_emitter := IntegerToken "" "u";
               numeral_converters := [] |} |}.

(** [N] is an [unsigned int]: [N0] is [0], [Npos p] is [p]. *)
#[export] Instance bde_n_mapping : TypeMapping N :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "unsigned int";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews N;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref N0;
             ctor_build := Expr "0u";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 0u";
                       case_fields := [] |} |};
          {| ctor_source := Ref Npos;
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut != 0u";
                       case_fields := [(0, OwnedProjection "%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref N0; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref Npos; numeral_action := NumeralIdentity 0 |}];
               numeral_emitter := IntegerToken "" "u";
               numeral_converters := [Ref N.of_num_uint] |} |}.

(* Pos operations *)
#[export] Instance bde_pos_add_mapping : OperationMapping (Ref Pos.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_sub_mapping : OperationMapping (Ref Pos.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) > %arg(y) ? %arg(x) - %arg(y) : 1u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_mul_mapping : OperationMapping (Ref Pos.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_succ_mapping : OperationMapping (Ref Pos.succ) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + 1u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_pred_mapping : OperationMapping (Ref Pos.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) > 1u ? %arg(x) - 1u : 1u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_eqb_mapping : OperationMapping (Ref Pos.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(p) == %arg(q)";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "q"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_ltb_mapping : OperationMapping (Ref Pos.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_leb_mapping : OperationMapping (Ref Pos.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_compare_mapping : OperationMapping (Ref Pos.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) < %arg(y) ? %ret::LT : (%arg(y) < %arg(x) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_eq_dec_mapping : OperationMapping (Ref Pos.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_min_mapping : OperationMapping (Ref Pos.min) :=
  {| operation_headers := ["bsl_algorithm.h"];
     operation_cpp := Expr "bsl::min(%arg(p), %arg(p'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "p'"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_max_mapping : OperationMapping (Ref Pos.max) :=
  {| operation_headers := ["bsl_algorithm.h"];
     operation_cpp := Expr "bsl::max(%arg(p), %arg(p'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "p'"; argument_use := Read |}]
         ReturnValue [] |}.

(* N operations *)
#[export] Instance bde_n_add_mapping : OperationMapping (Ref N.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_sub_mapping : OperationMapping (Ref N.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) >= %arg(m) ? %arg(n) - %arg(m) : 0u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_mul_mapping : OperationMapping (Ref N.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) * %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_div_mapping : OperationMapping (Ref N.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b) == 0u ? 0u : %arg(a) / %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_modulo_mapping : OperationMapping (Ref N.modulo) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b) == 0u ? %arg(a) : %arg(a) % %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_succ_mapping : OperationMapping (Ref N.succ) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + 1u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_pred_mapping : OperationMapping (Ref N.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) == 0u ? 0u : %arg(n) - 1u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_eqb_mapping : OperationMapping (Ref N.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_ltb_mapping : OperationMapping (Ref N.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_leb_mapping : OperationMapping (Ref N.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_compare_mapping : OperationMapping (Ref N.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) < %arg(m) ? %ret::LT : (%arg(m) < %arg(n) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_eq_dec_mapping : OperationMapping (Ref N.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_min_mapping : OperationMapping (Ref N.min) :=
  {| operation_headers := ["bsl_algorithm.h"];
     operation_cpp := Expr "bsl::min(%arg(n), %arg(n'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "n'"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_max_mapping : OperationMapping (Ref N.max) :=
  {| operation_headers := ["bsl_algorithm.h"];
     operation_cpp := Expr "bsl::max(%arg(n), %arg(n'))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "n'"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_double_mapping : OperationMapping (Ref N.double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) * 2u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_succ_double_mapping : OperationMapping (Ref N.succ_double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * 2u + 1u)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* Conversions.  A [nat] is whatever the [nat] mapping in force makes it
   ([unsigned int] under [Mapping.NatIntBDE]), so the conversions into it name
   the type their call yields, [%ret], rather than this mapping's width. *)
#[export] Instance bde_n_of_nat_mapping : OperationMapping (Ref N.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<unsigned int>(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_n_to_nat_mapping : OperationMapping (Ref N.to_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<%ret>(%arg(a))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_of_nat_mapping : OperationMapping (Ref Pos.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<unsigned int>(%arg(n) == 0u ? 1u : %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_pos_to_nat_mapping : OperationMapping (Ref Pos.to_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<%ret>(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
