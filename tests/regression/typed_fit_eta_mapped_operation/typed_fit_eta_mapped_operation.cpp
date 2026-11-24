#include "typed_fit_eta_mapped_operation.h"

uint64_t TypedFitEtaMappedOperation::use(const List<uint64_t> &l, bool) {
  auto _lc1_pa0 =
      l.template fold_right<std::optional<crane::fn<uint64_t(uint64_t)>>>(
          [](uint64_t,
             std::optional<crane::fn<uint64_t(uint64_t)>> acc) { return acc; },
          std::optional<crane::fn<uint64_t(uint64_t)>>{});
  crane::fn<uint64_t(uint64_t)> cf = [=](uint64_t _x0) -> uint64_t {
    return [](const auto &_m, auto _d) { return _m.has_value() ? *_m : _d; }(
        _lc1_pa0, crane::fn<uint64_t(uint64_t)>([](uint64_t x) { return x; }))(
        _x0);
  };
  return cf(UINT64_C(0));
}
