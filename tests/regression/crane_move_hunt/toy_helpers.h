#pragma once
#include <memory>
template <typename T>
inline void toy_tick(T s) {
  (void)s->core->payload;
}
template <typename T>
inline unsigned int toy_tick_nat(T s) {
  return s->core->payload;
}
