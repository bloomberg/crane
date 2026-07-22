#include "numeral_edge.h"

/// 6. Numeral as function argument
uint64_t NumeralEdge::take_nat(uint64_t n) { return (n + UINT64_C(1)); }

/// 10. Numeral in match
uint64_t NumeralEdge::classify(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t _x = n0 - 1;
      return UINT64_C(2);
    }
  }
}

/// 11. Comparison with numeral
bool NumeralEdge::is_big(uint64_t n) { return UINT64_C(100) <= n; }
