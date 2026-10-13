#include "three_argument_curried_slot.h"

uint64_t ThreeArgumentCurriedSlot::add3(uint64_t a, uint64_t b, uint64_t c) {
  return ((a + b) + c);
}

uint64_t ThreeArgumentCurriedSlot::f3(uint64_t x0_, uint64_t x1_,
                                      uint64_t x2_) {
  static const auto idp_1 = crane::immortal(
      idp<crane::fn<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(
          uint64_t)>>([](uint64_t _ec0) {
        return [=](uint64_t _ec1) {
          return [=](uint64_t _ec2) { return add3(_ec0, _ec1, _ec2); };
        };
      }));
  return crane::apply2(idp_1, x0_, x1_)(x2_);
}
