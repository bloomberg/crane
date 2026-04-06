#include <z_div_min.h>

#include <cassert>
#include <climits>
#include <cstdint>
#include <iostream>

int main() {
  // Verify int64_min is correct
  auto imin = ZDivMin::int64_min;
  std::cout << "int64_min = " << imin << std::endl;
  assert(imin == INT64_MIN);

  // INT64_MIN / -1: in Rocq, the result is 9223372036854775808 (positive).
  // In C++, signed division overflow is UB.
  // With UBSan this would trap; without it, typically returns INT64_MIN.
  auto d = ZDivMin::div_min_neg1;
  std::cout << "div_min_neg1 = " << d << std::endl;
  // The result should be positive (Rocq semantics)
  assert(d > 0);

  // INT64_MIN % -1: in Rocq, the result is 0.
  // In C++, also UB.
  auto m = ZDivMin::mod_min_neg1;
  std::cout << "mod_min_neg1 = " << m << std::endl;
  assert(m == 0);

  // Z.opp INT64_MIN: -(INT64_MIN) overflows int64_t → UB.
  // In Rocq, result is positive.
  auto o = ZDivMin::opp_min;
  std::cout << "opp_min = " << o << std::endl;
  assert(o > 0);

  auto opos = ZDivMin::opp_is_positive;
  std::cout << "opp_is_positive = " << opos << std::endl;
  assert(opos == true);

  std::cout << "All z_div_min tests passed!" << std::endl;
  return 0;
}
