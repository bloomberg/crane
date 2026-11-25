#include "twice_composed_fn_destination.h"

uint64_t TwiceComposedFnDestination::h(uint64_t k, uint64_t x0_) {
  return twice<crane::fn<uint64_t(uint64_t)>>(
      [&]() {
        crane::fn<uint64_t(uint64_t, uint64_t)> cf =
            [=](uint64_t y, uint64_t j) { return ((y + j) + k); };
        return [=, cf = std::move(cf)](const crane::fn<uint64_t(uint64_t)> &c) {
          return [=, c = c, cf = cf](uint64_t _pa0) {
            return cf(c(UINT64_C(1)), _pa0);
          };
        };
      }(),
      [](uint64_t j) { return (j * UINT64_C(10)); })(x0_);
}
