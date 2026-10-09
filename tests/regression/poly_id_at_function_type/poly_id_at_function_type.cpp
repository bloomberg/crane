#include "poly_id_at_function_type.h"

uint64_t PolyIdAtFunctionType::apply_id(uint64_t n) {
  static const auto id2_1 = crane::immortal(id2<crane::fn<uint64_t(uint64_t)>>(
      [](uint64_t k) { return (k + UINT64_C(1)); }));
  return id2_1(n);
}

uint64_t PolyIdAtFunctionType::apply_id2(uint64_t n) {
  static const auto id2_1 = crane::immortal(
      id2<crane::fn<crane::fn<uint64_t(uint64_t)>(
          crane::fn<uint64_t(uint64_t)>)>>([](crane::fn<uint64_t(uint64_t)> f) {
        return [=](uint64_t x) { return f(f(x)); };
      }));
  return crane::apply2(
      id2_1,
      [](uint64_t _x0) -> uint64_t {
        return id2<crane::fn<uint64_t(uint64_t)>>(
            [](uint64_t k) { return (k * UINT64_C(3)); })(_x0);
      },
      n);
}
