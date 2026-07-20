// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#ifndef CRANE_REAL_H
#define CRANE_REAL_H
#include <cmath>
#include <algorithm>
#include <cstdint>
#include <sstream>
#include <type_traits>

class Real {
  long double v_;
public:
  constexpr Real() : v_(0.0L) {}
  constexpr explicit Real(long double v) : v_(v) {}
  constexpr explicit Real(int64_t v) : v_(static_cast<long double>(v)) {}
  constexpr explicit Real(unsigned int v) : v_(static_cast<long double>(v)) {}

  // Arithmetic
  friend Real operator+(Real a, Real b) { return Real(a.v_ + b.v_); }
  friend Real operator-(Real a, Real b) { return Real(a.v_ - b.v_); }
  friend Real operator*(Real a, Real b) { return Real(a.v_ * b.v_); }
  friend Real operator/(Real a, Real b) { return Real(a.v_ / b.v_); }
  Real operator-() const { return Real(-v_); }

  // Comparison
  friend bool operator< (Real a, Real b) { return a.v_ <  b.v_; }
  friend bool operator<=(Real a, Real b) { return a.v_ <= b.v_; }
  friend bool operator==(Real a, Real b) { return a.v_ == b.v_; }
  friend bool operator!=(Real a, Real b) { return a.v_ != b.v_; }

  // Math (free functions for clean mapping syntax)
  friend Real r_inv(Real x) { return Real(1.0L / x.v_); }
  friend Real r_abs(Real x) { return Real(std::fabs(x.v_)); }
  friend Real r_sqrt(Real x) { return Real(std::sqrt(x.v_)); }
  friend Real r_sqr(Real x) { return Real(x.v_ * x.v_); }
  friend Real r_sin(Real x) { return Real(std::sin(x.v_)); }
  friend Real r_cos(Real x) { return Real(std::cos(x.v_)); }
  friend Real r_asin(Real x) { return Real(std::asin(x.v_)); }
  friend Real r_acos(Real x) { return Real(std::acos(x.v_)); }
  friend Real r_atan(Real x) { return Real(std::atan(x.v_)); }
  friend Real r_tan(Real x) { return Real(std::tan(x.v_)); }
  friend Real r_max(Real a, Real b) { return a.v_ >= b.v_ ? a : b; }
  friend Real r_min(Real a, Real b) { return a.v_ <= b.v_ ? a : b; }
  friend Real r_pow(Real b, unsigned int e) {
    return Real(std::pow(b.v_, static_cast<long double>(e)));
  }

  // Exponential & floor
  friend Real r_exp(Real x) { return Real(std::exp(x.v_)); }
  friend int64_t r_floor_z(Real x) {
    // Guard the floating-point -> int64_t conversion: casting NaN, an infinity,
    // or a value outside the int64_t range is undefined behaviour
    // (CWE-681 / CWE-682 / CWE-190).  Division and r_inv can produce
    // infinities, and sqrt/asin/acos can produce NaN from out-of-domain
    // inputs, either of which then reaches this cast.  Rocq's floor is total
    // over an idealized unbounded real, so keep the extracted version total
    // too: NaN maps to 0, and out-of-range magnitudes saturate to the int64_t
    // bounds rather than wrapping or trapping.
    long double f = std::floor(x.v_);
    if (std::isnan(f)) return 0;
    if (f >= 0x1p63L) return INT64_MAX;   // f >= 2^63
    if (f < -0x1p63L) return INT64_MIN;   // f < -2^63
    return static_cast<int64_t>(f);
  }
  friend std::string real_to_string(Real x) {
    std::ostringstream oss;
    oss << x.v_;
    return oss.str();
  }

  // Constants & conversions
  static Real pi() { return Real(std::acos(-1.0L)); }

  // Integer -> Real coercions (INR / IZR / IPR).  Templated so the *same*
  // mapping works with whatever integer representation the user imports for
  // nat / Z / positive -- int64_t and unsigned int (the Int flavors) or GMP's
  // mpz_class (the GMP flavor) -- without Real.v committing to one.  Arithmetic
  // types convert directly; a bignum is narrowed through its get_d() member
  // (only instantiated when T is such a type, so <gmpxx.h> is not required
  // here).  Real is finite precision, so this coercion is inherently lossy for
  // integers beyond the long double mantissa, regardless of the source type.
  template <class T> static long double to_long_double(const T &z) {
    if constexpr (std::is_arithmetic_v<T>)
      return static_cast<long double>(z);
    else
      return static_cast<long double>(z.get_d());
  }
  template <class T> static Real from_nat(const T &n) { return Real(to_long_double(n)); }
  template <class T> static Real from_z(const T &z) { return Real(to_long_double(z)); }
  template <class T> static Real from_pos(const T &p) { return Real(to_long_double(p)); }
};
#endif
