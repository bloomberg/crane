#include "poly_id_at_function_type.h"

uint64_t PolyIdAtFunctionType::apply_id(uint64_t n) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto id2_1 = crane::immortal(id2<crane::fn<uint64_t(uint64_t)>>(
      [](uint64_t k) { return (k + UINT64_C(1)); }));
  return id2_1(n);
}

uint64_t PolyIdAtFunctionType::apply_id2(uint64_t n) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto id2_1 = crane::immortal(id2<
      crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>(
      [](crane::fn<uint64_t(uint64_t)> f) {
        return [=, f = std::move(f)](uint64_t x) { return f(f(x)); };
      }));
  return crane::apply2(id2_1, id2<crane::fn<uint64_t(uint64_t)>>(
                                  [](uint64_t k) { return (k * UINT64_C(3)); }),
                       n);
}
