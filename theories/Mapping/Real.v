(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.ZInt.
From Stdlib Require Import Reals Rtrigo Ratan Rsqrt_def.

(** Extraction of [R] (axiomatized reals) to a C++ [Real] class
    wrapping [long double].

    Imports [Mapping.ZInt] which transitively provides:
    - [positive] / [N] -> [unsigned int]   (via [NInt.v])
    - [Z] -> [int64_t]                     (via [ZInt.v])
    - Standard mappings (option, pair, etc.) (via [Std.v])

    This short-circuits the constructive real infrastructure
    (ConstructiveCauchyReals, ClassicalDedekindReals, etc.)
    by mapping R and its operations directly to concrete C++. *)

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
Crane Extract Inlined Constant IPR_2 => "Real::from_pos(2u * %a0)".

(* --- Short-circuit constructive real infrastructure --- *)
Crane Extract Inlined Constant Rabst => "%a0".
Crane Extract Inlined Constant Rrepr => "%a0".

(* --- Skip R implementation modules ---
   RbaseSymbolsImpl and RinvImpl define R via constructive reals.
   Since all their exported constants are mapped above, skip
   the module structures to prevent broken C++ generation. *)
Crane Extract Skip Module Rdefinitions.RbaseSymbolsImpl.
Crane Extract Skip Module Rdefinitions.RinvImpl.
