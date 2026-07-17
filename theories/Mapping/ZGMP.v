(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.NGMP.
From Stdlib Require Import BinInt.

(** Extraction of [Z] (binary integers) to GMP [mpz_class].

    Builds on [NGMP.v] which already extracts [positive] and [N].
    Maps [Z] to [mpz_class] with GMP arbitrary-precision arithmetic.

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)

Crane Extract Inductive Z =>
  "mpz_class"
  [ "mpz_class(0)" "%a0" "(-%a0)" ]
  "if (%scrut == 0) { %br0 } else if (%scrut > 0) { mpz_class %b1a0 = %scrut; %br1 } else { mpz_class %b2a0 = -%scrut; %br2 }".

Crane Extract Numeral Z => "mpz_class(%n)".

(* Z operations *)
Crane Extract Inlined Constant Z.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Z.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant Z.mul => "(%a0 * %a1)".
(* Rocq's Z.div / Z.modulo use *floored* division (the remainder takes the sign
   of the divisor). GMP's mpz_class / and % truncate toward zero (remainder
   takes the sign of the dividend), so we apply the flooring correction to match
   Rocq for negative operands, following Rocq's a/0 = 0 and a mod 0 = a
   conventions for a zero divisor (CWE-682). *)
Crane Extract Inlined Constant Z.div =>
"[&]() -> mpz_class {
  mpz_class _a = %a0;
  mpz_class _b = %a1;
  if (_b == 0) return mpz_class(0);
  mpz_class _q = _a / _b;
  mpz_class _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _q - 1;
  return _q;
}()".
Crane Extract Inlined Constant Z.modulo =>
"[&]() -> mpz_class {
  mpz_class _a = %a0;
  mpz_class _b = %a1;
  if (_b == 0) return _a;
  mpz_class _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _r + _b;
  return _r;
}()".
Crane Extract Inlined Constant Z.opp => "(-%a0)".
Crane Extract Inlined Constant Z.abs => "abs(%a0)".
Crane Extract Inlined Constant Z.succ => "(%a0 + 1)".
Crane Extract Inlined Constant Z.pred => "(%a0 - 1)".
Crane Extract Inlined Constant Z.eqb => "%a0 == %a1".
Crane Extract Inlined Constant Z.ltb => "%a0 < %a1".
Crane Extract Inlined Constant Z.leb => "%a0 <= %a1".
Crane Extract Inlined Constant Z.gtb => "%a0 > %a1".
Crane Extract Inlined Constant Z.geb => "%a0 >= %a1".
Crane Extract Inlined Constant Z.min => "(%a0 <= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Z.max => "(%a0 >= %a1 ? %a0 : %a1)".

(* Conversions *)
Crane Extract Inlined Constant Z.of_nat => "mpz_class(%a0)".
(* [mpz_class::get_ui] only returns the low word of an arbitrary-precision
   value. Rocq's [Z.to_nat] is total (negatives map to 0) but places no upper
   bound on the result, so silently truncating a large positive value would
   produce a wrapped, wrong result instead of surfacing the loss of precision
   (CWE-190/CWE-681); we saturate at [UINT_MAX] instead. *)
Crane Extract Inlined Constant Z.to_nat =>
  "(%a0 < 0 ? 0 : (%a0 > mpz_class(UINT_MAX) ? UINT_MAX : static_cast<unsigned int>(%a0.get_ui())))"
  From "climits".
Crane Extract Inlined Constant Z.of_N => "mpz_class(%a0)".
Crane Extract Inlined Constant Z.to_N => "(%a0 < 0 ? mpz_class(0) : %a0)".
Crane Extract Inlined Constant Z.abs_N => "abs(%a0)".
