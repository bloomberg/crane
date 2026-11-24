#include "poly_instance_curried_fn.h"

std::optional<crane::fn<uint64_t(bool, uint64_t)>>
PolyInstanceCurriedFn::none_fn(bool) {
  return id2<crane::fn<uint64_t(bool, uint64_t)>>(
      std::optional<crane::fn<uint64_t(bool, uint64_t)>>());
}

uint64_t PolyInstanceCurriedFn::use_result(
    std::optional<crane::fn<uint64_t(bool, uint64_t)>> o) {
  auto _cs = id2<crane::fn<uint64_t(bool, uint64_t)>>(std::move(o));
  if (_cs.has_value()) {
    const crane::fn<uint64_t(bool, uint64_t)> &f = *_cs;
    return f(true, UINT64_C(1));
  } else {
    return UINT64_C(0);
  }
}

std::optional<crane::fn<uint64_t(bool, uint64_t)>> PolyInstanceCurriedFn::pass(
    std::optional<crane::fn<uint64_t(bool, uint64_t)>> x0_) {
  return id2<crane::fn<uint64_t(bool, uint64_t)>>(std::move(x0_));
}
