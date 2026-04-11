// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test harness for PrimFloat extraction — IEEE 754 binary64 arithmetic.

#include <prim_float.h>

#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // ---- Constants ----
  ASSERT(PrimFloat::f_zero == 0.0);
  ASSERT(PrimFloat::f_one == 1.0);
  ASSERT(PrimFloat::f_neg_one == -1.0);

  // ---- Basic arithmetic ----
  ASSERT(PrimFloat::test_add(2.5, 3.5) == 6.0);
  ASSERT(PrimFloat::test_sub(10.0, 3.0) == 7.0);
  ASSERT(PrimFloat::test_mul(4.0, 2.5) == 10.0);
  ASSERT(PrimFloat::test_div(10.0, 4.0) == 2.5);

  // ---- Unary ops ----
  ASSERT(PrimFloat::test_opp(5.0) == -5.0);
  ASSERT(PrimFloat::test_opp(-3.0) == 3.0);
  ASSERT(PrimFloat::test_abs(-7.0) == 7.0);
  ASSERT(PrimFloat::test_abs(7.0) == 7.0);
  ASSERT(PrimFloat::test_sqrt(4.0) == 2.0);
  ASSERT(PrimFloat::test_sqrt(9.0) == 3.0);

  // ---- Comparison ----
  ASSERT(PrimFloat::test_eqb(1.0, 1.0) == true);
  ASSERT(PrimFloat::test_eqb(1.0, 2.0) == false);
  ASSERT(PrimFloat::test_ltb(1.0, 2.0) == true);
  ASSERT(PrimFloat::test_ltb(2.0, 1.0) == false);
  ASSERT(PrimFloat::test_ltb(1.0, 1.0) == false);
  ASSERT(PrimFloat::test_leb(1.0, 2.0) == true);
  ASSERT(PrimFloat::test_leb(1.0, 1.0) == true);
  ASSERT(PrimFloat::test_leb(2.0, 1.0) == false);

  // ---- IEEE 754 special values ----
  [[maybe_unused]] constexpr double inf = std::numeric_limits<double>::infinity();
  [[maybe_unused]] constexpr double nan_val = std::numeric_limits<double>::quiet_NaN();

  // Division by zero produces infinity.
  ASSERT(std::isinf(PrimFloat::test_div(1.0, 0.0)));
  ASSERT(PrimFloat::test_div(1.0, 0.0) > 0); // +inf
  ASSERT(std::isinf(PrimFloat::test_div(-1.0, 0.0)));
  ASSERT(PrimFloat::test_div(-1.0, 0.0) < 0); // -inf

  // 0/0 = NaN.
  ASSERT(std::isnan(PrimFloat::test_div(0.0, 0.0)));

  // NaN propagation.
  ASSERT(std::isnan(PrimFloat::test_add(nan_val, 1.0)));
  ASSERT(std::isnan(PrimFloat::test_mul(nan_val, 0.0)));

  // NaN != NaN (IEEE 754).
  ASSERT(PrimFloat::test_eqb(nan_val, nan_val) == false);

  // NaN comparisons return false.
  ASSERT(PrimFloat::test_ltb(nan_val, 1.0) == false);
  ASSERT(PrimFloat::test_leb(nan_val, 1.0) == false);
  ASSERT(PrimFloat::test_ltb(1.0, nan_val) == false);

  // +0 == -0 (IEEE 754).
  ASSERT(PrimFloat::test_eqb(0.0, -0.0) == true);

  // ---- Conversion ----
  ASSERT(PrimFloat::test_of_uint63(42) == 42.0);
  ASSERT(PrimFloat::test_of_uint63(0) == 0.0);

  // ---- sqrt of NaN is NaN ----
  ASSERT(std::isnan(PrimFloat::test_sqrt(-1.0)));

  if (testStatus == 0) {
    std::cout << "All prim_float tests passed." << std::endl;
  }
  return testStatus;
}
