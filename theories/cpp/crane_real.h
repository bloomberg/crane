// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#ifndef CRANE_REAL_H
#define CRANE_REAL_H
#include <cmath>
#include <algorithm>

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
  friend Real r_abs(Real x) { return Real(std::fabsl(x.v_)); }
  friend Real r_sqrt(Real x) { return Real(std::sqrtl(x.v_)); }
  friend Real r_sqr(Real x) { return Real(x.v_ * x.v_); }
  friend Real r_sin(Real x) { return Real(std::sinl(x.v_)); }
  friend Real r_cos(Real x) { return Real(std::cosl(x.v_)); }
  friend Real r_asin(Real x) { return Real(std::asinl(x.v_)); }
  friend Real r_acos(Real x) { return Real(std::acosl(x.v_)); }
  friend Real r_atan(Real x) { return Real(std::atanl(x.v_)); }
  friend Real r_tan(Real x) { return Real(std::tanl(x.v_)); }
  friend Real r_max(Real a, Real b) { return a.v_ >= b.v_ ? a : b; }
  friend Real r_min(Real a, Real b) { return a.v_ <= b.v_ ? a : b; }
  friend Real r_pow(Real b, unsigned int e) {
    return Real(std::powl(b.v_, static_cast<long double>(e)));
  }

  // Constants & conversions
  static Real pi() { return Real(std::acosl(-1.0L)); }
  static Real from_nat(unsigned int n) { return Real(static_cast<long double>(n)); }
  static Real from_z(int64_t z) { return Real(static_cast<long double>(z)); }
  static Real from_pos(unsigned int p) { return Real(static_cast<long double>(p)); }
};
#endif
