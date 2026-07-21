#include "loopify_gap_if_condition.h"

uint64_t LoopifyGapIfCondition::parity(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    if (parity(m) == UINT64_C(0)) {
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  }
}
