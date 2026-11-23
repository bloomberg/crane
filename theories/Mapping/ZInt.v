(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.NInt Mapping.NatIntStd.
From Stdlib Require Import BinInt.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** Extraction of [Z] (binary integers) to [int64_t].

    Builds on [NInt.v], which already extracts [positive] and [N], and on
    [NatIntStd.v]: [Z.of_nat] and [Z.to_nat] are casts between machine
    integers, so this flavour only holds together if [nat] is one too.
    Maps [Z] to [int64_t] with native C++ arithmetic.
*)

(** [Z] is an [int64_t]: [Z0] is [0], [Zpos p] is [p], [Zneg p] is [-p]
    (the [positive] of [NInt] is an [unsigned int]); a numeral is an
    [INT64_C] literal. *)
#[export] Instance std_z_mapping : TypeMapping Z :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "int64_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Z;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Z0;
             ctor_build := Expr "INT64_C(0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 0";
                       case_fields := [] |} |};
          {| ctor_source := Ref Zpos;
             ctor_build := Expr "static_cast<int64_t>(%a0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut > 0";
                       case_fields := [(0, OwnedProjection "static_cast<unsigned int>(%scrut)")] |} |};
          {| ctor_source := Ref Zneg;
             ctor_build := Expr "(-static_cast<int64_t>(%a0))";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut < 0";
                       case_fields := [(0, OwnedProjection "static_cast<unsigned int>(-%scrut)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref Z0; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref Zpos; numeral_action := NumeralIdentity 0 |};
                  {| numeral_constructor := Ref Zneg; numeral_action := NumeralNegate 0 |}];
               numeral_emitter := IntegerToken "INT64_C(" ")";
               numeral_converters := [Ref Z.of_num_int; Ref Z.of_num_uint] |} |}.

(* Z operations.

   [Z] is unbounded in Rocq but represented as [int64_t] here, so operations
   that exceed the 64-bit range cannot match Rocq exactly. What we can and do
   guarantee is that they never execute C++ *undefined behavior*: signed
   overflow, negation/abs of INT64_MIN, and INT64_MIN / -1 are all UB, which an
   optimizer may miscompile in ways that silently invalidate the verified
   source's assumptions (CWE-190 / CWE-682). Each arithmetic op is therefore
   computed in the unsigned domain, where wraparound is well-defined, and cast
   back (C++20 mandates two's-complement, so the round-trip is defined). For
   inputs whose true result fits in int64_t this is identical to native signed
   arithmetic; only the out-of-range cases differ, and there they wrap
   deterministically instead of being UB. *)
#[export] Instance std_z_add_mapping : OperationMapping (Ref Z.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(static_cast<uint64_t>(%arg(x)) + static_cast<uint64_t>(%arg(y)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_sub_mapping : OperationMapping (Ref Z.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(static_cast<uint64_t>(%arg(m)) - static_cast<uint64_t>(%arg(n)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "m"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_mul_mapping : OperationMapping (Ref Z.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(static_cast<uint64_t>(%arg(x)) * static_cast<uint64_t>(%arg(y)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(* Rocq's Z.div / Z.modulo use *floored* division (the remainder takes the sign
   of the divisor), whereas C++ / and % truncate toward zero. We compute the
   truncated quotient/remainder once and apply the flooring correction so the
   results match Rocq for negative operands, and follow Rocq's a/0 = 0 and
   a mod 0 = a conventions for a zero divisor (CWE-682). The [_b == -1] case is
   handled separately because INT64_MIN / -1 and INT64_MIN % -1 are UB. *)
#[export] Instance std_z_div_mapping : OperationMapping (Ref Z.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "[](int64_t _a, int64_t _b) -> int64_t {
  if (_b == 0) return INT64_C(0);
  if (_b == -1) return static_cast<int64_t>(-static_cast<uint64_t>(_a));
  int64_t _q = _a / _b;
  int64_t _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _q - 1;
  return _q;
}(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_modulo_mapping : OperationMapping (Ref Z.modulo) :=
  {| operation_headers := [];
     operation_cpp := Expr "[](int64_t _a, int64_t _b) -> int64_t {
  if (_b == 0) return _a;
  if (_b == -1) return INT64_C(0);
  int64_t _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _r + _b;
  return _r;
}(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_opp_mapping : OperationMapping (Ref Z.opp) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(-static_cast<uint64_t>(%arg(x)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_abs_mapping : OperationMapping (Ref Z.abs) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(z) < 0 ? static_cast<int64_t>(-static_cast<uint64_t>(%arg(z))) : %arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_succ_mapping : OperationMapping (Ref Z.succ) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(static_cast<uint64_t>(%arg(x)) + 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_pred_mapping : OperationMapping (Ref Z.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(static_cast<uint64_t>(%arg(x)) - 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_eqb_mapping : OperationMapping (Ref Z.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_ltb_mapping : OperationMapping (Ref Z.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_leb_mapping : OperationMapping (Ref Z.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_gtb_mapping : OperationMapping (Ref Z.gtb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) > %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_geb_mapping : OperationMapping (Ref Z.geb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) >= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_compare_mapping : OperationMapping (Ref Z.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) < %arg(y) ? %ret::LT : (%arg(y) < %arg(x) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_eq_dec_mapping : OperationMapping (Ref Z.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_min_mapping : OperationMapping (Ref Z.min) :=
  {| operation_headers := ["algorithm"];
     operation_cpp := Expr "std::min(%arg(n), %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_max_mapping : OperationMapping (Ref Z.max) :=
  {| operation_headers := ["algorithm"];
     operation_cpp := Expr "std::max(%arg(n), %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.

(* Conversions *)
#[export] Instance std_z_of_nat_mapping : OperationMapping (Ref Z.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_to_nat_mapping : OperationMapping (Ref Z.to_nat) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<uint64_t>(%arg(z) < 0 ? 0 : %arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_of_N_mapping : OperationMapping (Ref Z.of_N) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_to_N_mapping : OperationMapping (Ref Z.to_N) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<unsigned int>(%arg(z) < 0 ? 0 : %arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_z_abs_N_mapping : OperationMapping (Ref Z.abs_N) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<unsigned int>(%arg(z) < 0 ? -static_cast<uint64_t>(%arg(z)) : static_cast<uint64_t>(%arg(z)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
