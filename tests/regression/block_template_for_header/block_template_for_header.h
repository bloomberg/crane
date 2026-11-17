#pragma once

#include <cstdint>

struct BlockTemplateForHeader {
  static uint64_t next_after(uint64_t n);
  static inline const uint64_t past_ten = []() -> uint64_t {
    uint64_t _r;
    for (unsigned int _i = 0;; ++_i) {
      if (_i >= UINT64_C(10)) {
        _r = _i;
        break;
      }
    };
    return _r;
  }();
};
