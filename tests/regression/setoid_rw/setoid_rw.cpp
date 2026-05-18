#include "setoid_rw.h"

uint64_t SetoidRw::mod3(uint64_t n) {
  return (UINT64_C(3) ? n % UINT64_C(3) : n);
}

uint64_t SetoidRw::classify_mod3(uint64_t n) {
  auto _cs = mod3(n);
  if (_cs <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = _cs - 1;
    if (n0 <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t _x = n0 - 1;
      return UINT64_C(2);
    }
  }
}

uint64_t SetoidRw::add_mod3(uint64_t x, uint64_t y) { return mod3((x + y)); }
