#include "itree_two_self_calls.h"

/// Visits the midpoints of l..r, left half first; fuel bounds the
/// depth.
void ItreeTwoSelfCalls::walk(uint64_t fuel, uint64_t l, uint64_t r) {
  if (fuel <= 0) {
    return;
  } else {
    uint64_t f = fuel - 1;
    if (l < r) {
      uint64_t p = (UINT64_C(2) ? (l + r) / UINT64_C(2) : 0);
      walk(f, l, (((p - UINT64_C(1)) > p ? 0 : (p - UINT64_C(1)))));
      walk(f, (p + UINT64_C(1)), r);
      return;
    } else {
      return;
    }
  }
}

void ItreeTwoSelfCalls::run(uint64_t n) {
  walk(n, UINT64_C(0), n);
  return;
}
