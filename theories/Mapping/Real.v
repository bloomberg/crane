(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Stdlib Require Import Reals Rtrigo Ratan Rsqrt_def.

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

(* --- R type --- *)
Crane Extract Inlined Constant R => "Real" From "crane_real.h".

(* --- Core field operations --- *)
Crane Extract Inlined Constant R0 => "Real(0.0L)" From "crane_real.h".
Crane Extract Inlined Constant R1 => "Real(1.0L)" From "crane_real.h".
Crane Extract Inlined Constant Rplus => "(%a0 + %a1)".
Crane Extract Inlined Constant Rmult => "(%a0 * %a1)".
Crane Extract Inlined Constant Ropp => "(-%a0)".
Crane Extract Inlined Constant Rinv => "r_inv(%a0)".
Crane Extract Inlined Constant Rminus => "(%a0 - %a1)".
Crane Extract Inlined Constant Rdiv => "(%a0 / %a1)".

(* --- Utility functions --- *)
Crane Extract Inlined Constant Rabs => "r_abs(%a0)".
Crane Extract Inlined Constant Rsqr => "r_sqr(%a0)".
Crane Extract Inlined Constant Rmax => "r_max(%a0, %a1)".
Crane Extract Inlined Constant Rmin => "r_min(%a0, %a1)".

(* --- Power / sqrt --- *)
Crane Extract Inlined Constant pow => "r_pow(%a0, %a1)".
Crane Extract Inlined Constant sqrt => "r_sqrt(%a0)".

(* --- Trigonometry --- *)
Crane Extract Inlined Constant sin => "r_sin(%a0)".
Crane Extract Inlined Constant cos => "r_cos(%a0)".
Crane Extract Inlined Constant tan => "r_tan(%a0)".
Crane Extract Inlined Constant asin => "r_asin(%a0)".
Crane Extract Inlined Constant acos => "r_acos(%a0)".
Crane Extract Inlined Constant atan => "r_atan(%a0)".
Crane Extract Inlined Constant PI => "Real::pi()".

(* --- Decision procedures (return sumbool -> bool) --- *)
Crane Extract Inlined Constant Rle_dec => "(%a0 <= %a1)".
Crane Extract Inlined Constant Rlt_dec => "(%a0 < %a1)".
Crane Extract Inlined Constant Req_EM_T => "(%a0 == %a1)".

(* --- Coercions --- *)
Crane Extract Inlined Constant INR => "Real::from_nat(%a0)".
Crane Extract Inlined Constant IZR => "Real::from_z(%a0)".
Crane Extract Inlined Constant IPR => "Real::from_pos(%a0)".
(* [IPR_2 p = 2 * IPR p]; double in real arithmetic rather than doing [2 * p] in
   the integer domain, so this stays independent of the integer representation
   (e.g. avoids relying on [unsigned]-typed multiplication). *)
Crane Extract Inlined Constant IPR_2 => "(Real::from_pos(%a0) + Real::from_pos(%a0))".

(* --- Short-circuit constructive real infrastructure --- *)
Crane Extract Inlined Constant Rabst => "%a0".
Crane Extract Inlined Constant Rrepr => "%a0".

(* --- Skip R implementation modules ---
   RbaseSymbolsImpl and RinvImpl define R via constructive reals.
   Since all their exported constants are mapped above, skip
   the module structures to prevent broken C++ generation. *)
Crane Extract Skip Module Rdefinitions.RbaseSymbolsImpl.
Crane Extract Skip Module Rdefinitions.RinvImpl.
