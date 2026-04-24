#include <z_abs_min.h>

#include <cstdint>
#include <cstdlib>
#include <type_traits>

/// In Rocq, Z.abs is total: Z.abs z is always non-negative.
/// ZInt maps Z.abs to std::abs(%a0) (from <cstdlib>).
/// But std::abs(INT64_MIN) is undefined behavior in C++
/// because -INT64_MIN cannot be represented as int64_t.
__attribute__((pure)) int64_t ZAbsMin::my_abs(const int64_t &_x0) {
  return std::abs(_x0);
}

/// Should always be true for Z.abs, but fails in C++.
__attribute__((pure)) bool ZAbsMin::is_nonneg(const int64_t &x) {
  return INT64_C(0) <= std::abs(x);
}
