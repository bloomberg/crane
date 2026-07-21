#include "loopify_gap_mutual3.h"

uint64_t LoopifyGapMutual3::rot_a(uint64_t n) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t k = _loop_n - 1;
      uint64_t _inl_n = k;
      if (_inl_n <= 0) {
        return UINT64_C(1);
      } else {
        uint64_t k = _inl_n - 1;
        uint64_t _inl_n = k;
        if (_inl_n <= 0) {
          return UINT64_C(2);
        } else {
          uint64_t k = _inl_n - 1;
          _loop_n = k;
        }
      }
    }
  }
}

uint64_t LoopifyGapMutual3::rot_b(uint64_t n) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t k = _loop_n - 1;
      uint64_t _inl_n = k;
      if (_inl_n <= 0) {
        return UINT64_C(2);
      } else {
        uint64_t k = _inl_n - 1;
        uint64_t _inl_n = k;
        if (_inl_n <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t k = _inl_n - 1;
          _loop_n = k;
        }
      }
    }
  }
}

uint64_t LoopifyGapMutual3::rot_c(uint64_t n) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return UINT64_C(2);
    } else {
      uint64_t k = _loop_n - 1;
      uint64_t _inl_n = k;
      if (_inl_n <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t k = _inl_n - 1;
        uint64_t _inl_n = k;
        if (_inl_n <= 0) {
          return UINT64_C(1);
        } else {
          uint64_t k = _inl_n - 1;
          _loop_n = k;
        }
      }
    }
  }
}
