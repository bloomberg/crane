// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression for the Real floor guard (crane_real.h): flooring a NaN, an
// infinity, or a value outside the int64_t range to int64_t must not invoke
// undefined behaviour.  Rocq's floor is total, so r_floor_z stays total —
// NaN maps to 0 and out-of-range magnitudes saturate to the int64_t bounds.

#include "real_floor_guard.h"

#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>

int main() {
  // Ordinary values floor as usual.
  assert(r_floor_z(Real(3.7L)) == 3);
  assert(r_floor_z(Real(-2.5L)) == -3);
  assert(r_floor_z(Real(0.0L)) == 0);
  assert(r_floor_z(Real(-0.0L)) == 0);

  // Non-finite and out-of-range inputs must be total, not UB.
  const long double inf = std::numeric_limits<long double>::infinity();
  const long double nan = std::numeric_limits<long double>::quiet_NaN();
  assert(r_floor_z(Real(inf)) == INT64_MAX);
  assert(r_floor_z(Real(-inf)) == INT64_MIN);
  assert(r_floor_z(Real(nan)) == 0);
  assert(r_floor_z(Real(1e30L)) == INT64_MAX);
  assert(r_floor_z(Real(-1e30L)) == INT64_MIN);

  // A value produced by division-by-zero (infinity) also stays safe.
  assert(r_floor_z(Real(1.0L) / Real(0.0L)) == INT64_MAX);

  std::cout << "All real_floor_guard tests passed!" << std::endl;
  return 0;
}
