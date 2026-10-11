#include "projection_result_overapplied.h"

uint64_t ProjectionResultOverapplied::getf(
    const std::pair<crane::fn<uint64_t(uint64_t, uint64_t)>, uint64_t> &x0_,
    uint64_t x1_, uint64_t x2_) {
  return x0_.first(x1_)(x2_);
}

uint64_t ProjectionResultOverapplied::apply_snd(
    const std::pair<uint64_t, crane::fn<uint64_t(uint64_t, uint64_t)>> &p) {
  return p.second(p.first)(UINT64_C(10));
}
