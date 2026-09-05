#include "poly_id_at_function_type.h"

uint64_t PolyIdAtFunctionType::apply_id(uint64_t n) {
  return id2<std::function<uint64_t(uint64_t)>>(
      [](uint64_t k) { return (k + UINT64_C(1)); })(n);
}

uint64_t PolyIdAtFunctionType::apply_id2(uint64_t n) {
  return id2<std::function<std::function<uint64_t(uint64_t)>(
      std::function<uint64_t(uint64_t)>)>>(
      [](std::function<uint64_t(uint64_t)> f) {
        return [=](uint64_t x) mutable { return f(f(x)); };
      })(
      [](uint64_t _x0) -> uint64_t {
        return id2<std::function<uint64_t(uint64_t)>>(
            [](uint64_t k) { return (k * UINT64_C(3)); }, _x0);
      },
      n);
}
