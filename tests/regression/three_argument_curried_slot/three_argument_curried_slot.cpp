#include "three_argument_curried_slot.h"

uint64_t ThreeArgumentCurriedSlot::add3(uint64_t a, uint64_t b, uint64_t c) {
  return a + b + c;
}

uint64_t ThreeArgumentCurriedSlot::f3(uint64_t x0_, uint64_t x1_,
                                      uint64_t x2_) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto idp_1 = crane::immortal(
      idp<crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)>>(add3));
  return idp_1(x0_, x1_, x2_);
}
