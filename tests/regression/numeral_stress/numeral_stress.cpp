#include "numeral_stress.h"

/// 6. Numeral inside a fixpoint
uint64_t NumeralStress::count_from(uint64_t n, uint64_t target) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    if (n == target) {
      return n;
    } else {
      return count_from(n_, target);
    }
  }
}

/// 9. Numeral in boolean expression
bool NumeralStress::check_range(uint64_t n) {
  return (UINT64_C(10) <= n && n <= UINT64_C(100));
}

/// 10. Mixed nat and Z in one function
int64_t NumeralStress::mixed_arith(uint64_t n) {
  return (static_cast<int64_t>(n) + INT64_C(100));
}
