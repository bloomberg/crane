#include "prim_float.h"

double PrimFloat::test_add(double x0_, double x1_) { return (x0_ + x1_); }

double PrimFloat::test_sub(double x0_, double x1_) { return (x0_ - x1_); }

double PrimFloat::test_mul(double x0_, double x1_) { return (x0_ * x1_); }

double PrimFloat::test_div(double x0_, double x1_) { return (x0_ / x1_); }

double PrimFloat::test_opp(double x0_) { return (-x0_); }

double PrimFloat::test_abs(double x0_) { return std::abs(x0_); }

double PrimFloat::test_sqrt(double x0_) { return std::sqrt(x0_); }

bool PrimFloat::test_eqb(double x0_, double x1_) { return x0_ == x1_; }

bool PrimFloat::test_ltb(double x0_, double x1_) { return x0_ < x1_; }

bool PrimFloat::test_leb(double x0_, double x1_) { return x0_ <= x1_; }

double PrimFloat::test_of_uint63(int64_t x0_) {
  return static_cast<double>(x0_);
}
