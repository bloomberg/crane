#include "loopify_gap_mutual3.h"

uint64_t LoopifyGapMutual3::rot_a(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t k = n - 1;
    return rot_b(k);
  }
}

uint64_t LoopifyGapMutual3::rot_b(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t k = n - 1;
    return rot_c(k);
  }
}

uint64_t LoopifyGapMutual3::rot_c(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(2);
  } else {
    uint64_t k = n - 1;
    return rot_a(k);
  }
}
