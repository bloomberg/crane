#pragma once
#include <cstdint>

inline int eta_ticks = 0;
inline uint64_t eta_tick(uint64_t n) {
  ++eta_ticks;
  return n;
}
