// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The PrimFloat primitives the typed float mappings (theories/Mapping/
// StdCore.v, BDE.v) spell as calls.  A float is a double; each function
// follows Rocq's kernel (kernel/float64_common.ml) exactly.  A result that
// is a Rocq inductive -- a pair, a float_comparison -- is built at the type
// the mapping names, as in crane_int63.h.  Flavor independent.

#pragma once

#include <cmath>
#include <cstdint>
#include <limits>

namespace crane {

// PrimFloat.compare, as the float_comparison enum: FEq, FLt, FGt,
// FNotComparable in declaration order.
template <class FloatComparison>
FloatComparison float_compare(double x, double y) {
  return static_cast<FloatComparison>(x < y ? 1 : (x > y ? 2 : (x == y ? 0 : 3)));
}

// PrimFloat.normfr_mantissa: |f| * 2^53 where 0.5 <= |f| < 1, else 0.
inline std::int64_t float_normfr_mantissa(double f) {
  double a = std::fabs(f);
  return (a >= 0.5 && a < 1.0) ? static_cast<std::int64_t>(std::ldexp(a, 53)) : 0;
}

// The shift Rocq adds to an exponent to keep it an int63: 2 * emax + prec.
inline constexpr std::int64_t float_eshift = 2101;

// PrimFloat.frshiftexp: (m, e + eshift) where f = m * 2^e and
// 0.5 <= |m| < 1; (f, 0) for a zero, an infinity or a NaN.
template <class Pair> Pair float_frshiftexp(double f) {
  int c = std::fpclassify(f);
  if (c == FP_ZERO || c == FP_INFINITE || c == FP_NAN) {
    return Pair{f, 0};
  }
  int e = 0;
  double m = std::frexp(f, &e);
  return Pair{m, static_cast<std::int64_t>(e) + float_eshift};
}

// PrimFloat.ldshiftexp f e: f * 2^(min(e, 2 * eshift) - eshift).
inline double float_ldshiftexp(double f, std::int64_t e) {
  std::int64_t k = (e < 2 * float_eshift ? e : 2 * float_eshift) - float_eshift;
  return std::ldexp(f, static_cast<int>(k));
}

// PrimFloat.next_up / next_down.
inline double float_next_up(double f) {
  return std::nextafter(f, std::numeric_limits<double>::infinity());
}

inline double float_next_down(double f) {
  return std::nextafter(f, -std::numeric_limits<double>::infinity());
}

} // namespace crane
