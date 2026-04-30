#include <numeral_stress.h>

/// 6. Numeral inside a fixpoint
unsigned int NumeralStress::count_from(unsigned int n,
                                       const unsigned int &target) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    if (n == target) {
      return n;
    } else {
      return count_from(n_, target);
    }
  }
}

/// 9. Numeral in boolean expression
bool NumeralStress::check_range(const unsigned int &n) {
  return (10u <= n && n <= 100u);
}

/// 10. Mixed nat and Z in one function
int64_t NumeralStress::mixed_arith(const unsigned int &n) {
  return (static_cast<int64_t>(n) + INT64_C(100));
}
