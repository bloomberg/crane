#include "loopify_gap_mutual3.h"

uint64_t LoopifyGapMutual3::rot_a(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t k = _loop_n - 1;
      if (k <= 0) {
        return UINT64_C(1);
      } else {
        uint64_t k0 = k - 1;
        if (k0 <= 0) {
          return UINT64_C(2);
        } else {
          uint64_t k1 = k0 - 1;
          _loop_n = k1;
        }
      }
    }
  }
}

uint64_t LoopifyGapMutual3::rot_b(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t k = _loop_n - 1;
      if (k <= 0) {
        return UINT64_C(2);
      } else {
        uint64_t k0 = k - 1;
        if (k0 <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t k1 = k0 - 1;
          _loop_n = k1;
        }
      }
    }
  }
}

uint64_t LoopifyGapMutual3::rot_c(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return UINT64_C(2);
    } else {
      uint64_t k = _loop_n - 1;
      if (k <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t k0 = k - 1;
        if (k0 <= 0) {
          return UINT64_C(1);
        } else {
          uint64_t k1 = k0 - 1;
          _loop_n = k1;
        }
      }
    }
  }
}
