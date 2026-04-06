#include <z_abs_min.h>

#include <cassert>
#include <climits>
#include <cstdint>
#include <iostream>

int main() {
  // Basic sanity: abs(-42) = 42
  auto r1 = ZAbsMin::my_abs(INT64_C(-42));
  std::cout << "abs(-42) = " << r1 << std::endl;
  assert(r1 == 42);

  // The bug: std::abs(INT64_MIN) is undefined behavior in C++.
  // In Rocq, Z.abs is total and Z.abs int64_min > 0.
  // In C++, std::abs(INT64_MIN) typically returns INT64_MIN (negative!).
  //
  // Note: abs_of_min is a static inline const, so the UB actually
  // happens at static initialization time, before main() even starts!
  auto r2 = ZAbsMin::abs_of_min;
  std::cout << "abs_of_min = " << r2 << std::endl;
  // In Rocq this is positive; in C++ it's negative (INT64_MIN)
  assert(r2 > 0);

  // Also test via the is_nonneg wrapper — calls std::abs at runtime
  auto r3 = ZAbsMin::is_nonneg(INT64_MIN);
  std::cout << "is_nonneg(INT64_MIN) = " << r3 << std::endl;
  // In Rocq: always true. In C++: false (abs returns negative).
  assert(r3 == true);

  return 0;
}
