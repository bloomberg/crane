#include <numeral_stress.h>

#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// 6. Numeral inside a fixpoint
__attribute__((pure)) unsigned int
NumeralStress::count_from(const unsigned int n, const unsigned int target) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    if (n == target) {
      return std::move(n);
    } else {
      return count_from(n_, target);
    }
  }
}

/// 9. Numeral in boolean expression
__attribute__((pure)) bool NumeralStress::check_range(const unsigned int n) {
  return (10u <= n && n <= 100u);
}

/// 10. Mixed nat and Z in one function
__attribute__((pure)) int64_t NumeralStress::mixed_arith(const unsigned int n) {
  return (static_cast<int64_t>(n) + INT64_C(100));
}
