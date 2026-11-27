(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [R] (axiomatized reals) to a C++ [Real] class
    wrapping [long double].

    This mapping is deliberately *integer-flavor-agnostic*: it does not choose a
    representation for [Z] / [N] / [positive].  Only the four integer -> real
    coercions ([INR], [IZR], [IPR], [IPR_2]) touch those types, and they map to
    the templated [Real::from_nat] / [from_z] / [from_pos] helpers, which accept
    whatever C++ type the imported integer mapping uses (int64_t, unsigned int,
    or GMP [mpz_class]).  A program that uses those coercions must therefore
    import an integer flavor as well, e.g.:

    - [From Crane Require Import Mapping.ZInt Mapping.Real.]   (Z -> int64_t)
    - [From Crane Require Import Mapping.ZGMP Mapping.Real.]   (Z -> mpz_class)

    Keeping the choice out of [Real.v] means importing reals no longer silently
    pins [Z] to int64_t (which used to collide with an explicit GMP import).

    Only [Std] (option, pair, string, ...) is exported here, since it carries no
    integer-inductive mapping.  This short-circuits the constructive real
    infrastructure (ConstructiveCauchyReals, ClassicalDedekindReals, etc.) by
    mapping R and its operations directly to concrete C++. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Stdlib Require Import Reals Rtrigo Ratan Rsqrt_def.

From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** [R] is the [Real] class, a [long double] (BitCopy, read by value), and
    its operations are pure operation mappings (typed mappings:
    they activate on [Import]).  [R0], [R1]
    and [PI] are operations of no argument.  The decision procedures
    return the [bool] a [sumbool] is.  [Rabst] and [Rrepr] are the
    identity, short-circuiting the constructive real infrastructure. *)
#[export] Instance real_mapping : TypeMapping R :=
  {| type_headers := ["crane_real.h"];
     type_cpp := Crane.Cpp.Name "Real";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews R;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance real_r0_mapping : OperationMapping (Ref R0) :=
  {| operation_headers := ["crane_real.h"];
     operation_cpp := Expr "Real(0.0L)";
     operation_contract :=
       PureOperation [] ReturnValue [] |}.
#[export] Instance real_r1_mapping : OperationMapping (Ref R1) :=
  {| operation_headers := ["crane_real.h"];
     operation_cpp := Expr "Real(1.0L)";
     operation_contract :=
       PureOperation [] ReturnValue [] |}.
#[export] Instance real_rplus_mapping : OperationMapping (Ref Rplus) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) + %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rmult_mapping : OperationMapping (Ref Rmult) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) * %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_ropp_mapping : OperationMapping (Ref Ropp) :=
  {| operation_headers := [];
     operation_cpp := Expr "(-%arg(r))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rinv_mapping : OperationMapping (Ref Rinv) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_inv(%arg(r))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rminus_mapping : OperationMapping (Ref Rminus) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) - %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rdiv_mapping : OperationMapping (Ref Rdiv) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) / %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rabs_mapping : OperationMapping (Ref Rabs) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_abs(%arg(r))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rsqr_mapping : OperationMapping (Ref Rsqr) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_sqr(%arg(r))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rmax_mapping : OperationMapping (Ref Rmax) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_max(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rmin_mapping : OperationMapping (Ref Rmin) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_min(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_pow_mapping : OperationMapping (Ref pow) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_pow(%arg(r), %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_sqrt_mapping : OperationMapping (Ref sqrt) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_sqrt(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_sin_mapping : OperationMapping (Ref sin) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_sin(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_cos_mapping : OperationMapping (Ref cos) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_cos(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_tan_mapping : OperationMapping (Ref tan) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_tan(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_asin_mapping : OperationMapping (Ref asin) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_asin(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_acos_mapping : OperationMapping (Ref acos) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_acos(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_atan_mapping : OperationMapping (Ref atan) :=
  {| operation_headers := [];
     operation_cpp := Expr "r_atan(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_pi_mapping : OperationMapping (Ref PI) :=
  {| operation_headers := [];
     operation_cpp := Expr "Real::pi()";
     operation_contract :=
       PureOperation [] ReturnValue [] |}.
#[export] Instance real_rle_dec_mapping : OperationMapping (Ref Rle_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) <= %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rlt_dec_mapping : OperationMapping (Ref Rlt_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) < %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_req_em_t_mapping : OperationMapping (Ref Req_EM_T) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(r1) == %arg(r2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "r1"; argument_use := Read |};
          {| argument_name := "r2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_inr_mapping : OperationMapping (Ref INR) :=
  {| operation_headers := [];
     operation_cpp := Expr "Real::from_nat(%arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_izr_mapping : OperationMapping (Ref IZR) :=
  {| operation_headers := [];
     operation_cpp := Expr "Real::from_z(%arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_ipr_mapping : OperationMapping (Ref IPR) :=
  {| operation_headers := [];
     operation_cpp := Expr "Real::from_pos(%arg(p))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_ipr_2_mapping : OperationMapping (Ref IPR_2) :=
  {| operation_headers := [];
     operation_cpp := Expr "(Real::from_pos(%arg(p)) + Real::from_pos(%arg(p)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rabst_mapping : OperationMapping (Ref Rabst) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance real_rrepr_mapping : OperationMapping (Ref Rrepr) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* --- Skip R implementation modules ---
   RbaseSymbolsImpl and RinvImpl define R via constructive reals.
   Since all their exported constants are mapped above, skip
   the module structures to prevent broken C++ generation. *)
Crane Extract Skip Module Rdefinitions.RbaseSymbolsImpl.
Crane Extract Skip Module Rdefinitions.RinvImpl.
