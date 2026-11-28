(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [Z] (binary integers) to [int64_t] with native C++
    arithmetic: the mappings both flavours share; [ZInt.v] (std) and
    [ZIntBDE.v] select them, building on [NInt.v] / [NIntBDE.v], which
    extract [positive] and [N], and on [NatInt.v] / [NatIntBDE.v]: [Z.of_nat]
    and [Z.to_nat] are casts between machine integers, so a flavour only
    holds together if [nat] is one too. *)
From Crane Require Extraction.
From Stdlib Require Import BinInt.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.
Import Crane.Cpp.

(** [Z] is an [int64_t]: [Z0] is [0], [Zpos p] is [p], [Zneg p] is [-p]
    (the [positive] of [NInt] is an [unsigned int]); a numeral is an
    [INT64_C] literal. *)
Definition z_mapping : TypeMapping Z :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Int Crane.Cpp.I64;
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
(** [Z.add] is [+] wrapping modulo 2^64, never signed overflow. *)
Definition z_add_mapping : OperationMapping (Ref Z.add) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Wrapping) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.sub] is [-] wrapping modulo 2^64, never signed overflow. *)
Definition z_sub_mapping : OperationMapping (Ref Z.sub) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Sub Wrapping) (Arg "m") (Arg "n"));
     operation_contract :=
       PureOperation
         [{| argument_name := "m"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.mul] is [*] wrapping modulo 2^64, never signed overflow. *)
Definition z_mul_mapping : OperationMapping (Ref Z.mul) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Mul Wrapping) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.div] and [Z.modulo] floor (the remainder takes the divisor's sign),
    whereas C++ [/] and [%] truncate toward zero: the truncated quotient or
    remainder is corrected for operands of opposite sign.  A zero divisor
    follows Rocq ([a / 0 = 0], [a mod 0 = a]), and [b = -1] is answered
    without dividing, since [INT64_MIN / -1] is undefined behaviour. *)
Definition z_div_mapping : OperationMapping (Ref Z.div) :=
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
(** [Z.modulo]: the floored remainder, as for [z_div_mapping]. *)
Definition z_modulo_mapping : OperationMapping (Ref Z.modulo) :=
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
(** [Z.opp] negates in [uint64_t], so [-INT64_MIN] wraps to [INT64_MIN]
    instead of being undefined. *)
Definition z_opp_mapping : OperationMapping (Ref Z.opp) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Unop Negate (wrap U64 (Arg "x"))));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.abs] negates negatives in [uint64_t]; [INT64_MIN] stays itself. *)
Definition z_abs_mapping : OperationMapping (Ref Z.abs) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Less (Arg "z") (lit 0)) (wrap I64 (Unop Negate (wrap U64 (Arg "z")))) (Arg "z"));
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.succ] is [x + 1] in [uint64_t]; wraps at [INT64_MAX]. *)
Definition z_succ_mapping : OperationMapping (Ref Z.succ) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Binop (Add Unchecked) (wrap U64 (Arg "x")) (lit 1)));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.pred] is [x - 1] in [uint64_t]; wraps at [INT64_MIN]. *)
Definition z_pred_mapping : OperationMapping (Ref Z.pred) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Binop (Sub Unchecked) (wrap U64 (Arg "x")) (lit 1)));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.eqb] is [==]. *)
Definition z_eqb_mapping : OperationMapping (Ref Z.eqb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.ltb] is [<]. *)
Definition z_ltb_mapping : OperationMapping (Ref Z.ltb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Less (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.leb] is [<=]. *)
Definition z_leb_mapping : OperationMapping (Ref Z.leb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop LessEq (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.gtb] is [>]. *)
Definition z_gtb_mapping : OperationMapping (Ref Z.gtb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Greater (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.geb] is [>=]. *)
Definition z_geb_mapping : OperationMapping (Ref Z.geb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop GreaterEq (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.compare] is two [<] tests yielding [Lt], [Gt] or [Eq]. *)
Definition z_compare_mapping : OperationMapping (Ref Z.compare) :=
  {| operation_headers := [];
     operation_cpp := Structured (three_way (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.eq_dec] is [==]: the [sumbool] is a [bool]. *)
Definition z_eq_dec_mapping : OperationMapping (Ref Z.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.min] is the flavour's [min] ([std::min] or [bsl::min]). *)
Definition z_min_mapping (f : Flavour) : OperationMapping (Ref Z.min) :=
  {| operation_headers := [(flavour_algorithm f)];
     operation_cpp := Structured (Call (flavour_min f) [] [(Arg "n"); (Arg "m")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.max] is the flavour's [max] ([std::max] or [bsl::max]). *)
Definition z_max_mapping (f : Flavour) : OperationMapping (Ref Z.max) :=
  {| operation_headers := [(flavour_algorithm f)];
     operation_cpp := Structured (Call (flavour_max f) [] [(Arg "n"); (Arg "m")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.

(* Conversions *)
(** [Z.of_nat] wraps the [nat] into [int64_t]: a [uint64_t] at or above
    2^63 turns negative. *)
Definition z_of_nat_mapping : OperationMapping (Ref Z.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Arg "n"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.to_nat] clamps negatives to [0], then wraps into the [nat] type. *)
Definition z_to_nat_mapping : OperationMapping (Ref Z.to_nat) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Wrap ResultType (Cond (Binop Less (Arg "z") (lit 0)) (lit 0) (Arg "z")));
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.of_N] widens the [unsigned int] to [int64_t]. *)
Definition z_of_N_mapping : OperationMapping (Ref Z.of_N) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Arg "n"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.to_N] clamps negatives to [0], then wraps into the [N] type,
    dropping bits above [UINT_MAX]. *)
Definition z_to_N_mapping : OperationMapping (Ref Z.to_N) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Wrap ResultType (Cond (Binop Less (Arg "z") (lit 0)) (lit 0) (Arg "z")));
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [Z.abs_N] takes the magnitude in [uint64_t], then wraps into the [N]
    type. *)
Definition z_abs_N_mapping : OperationMapping (Ref Z.abs_N) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Wrap ResultType (Cond (Binop Less (Arg "z") (lit 0)) (Unop Negate (wrap U64 (Arg "z"))) (wrap U64 (Arg "z"))));
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
