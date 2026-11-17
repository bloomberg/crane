// A payload that counts its copies, for last_use_places.
#pragma once
#include <cstdint>

struct Big {
  uint64_t v;
  static inline int copies = 0;
  explicit Big(uint64_t v) : v(v) {}
  Big(const Big &o) : v(o.v) { ++copies; }
  Big(Big &&o) noexcept : v(o.v) { o.v = 0; }
  Big &operator=(const Big &o) {
    v = o.v;
    ++copies;
    return *this;
  }
  Big &operator=(Big &&o) noexcept {
    v = o.v;
    o.v = 0;
    return *this;
  }
};

// Reads its argument twice: a move written into it would leave the second
// read with a moved-from value.
inline uint64_t sum_twice(const Big &a, const Big &b) { return a.v + b.v; }
