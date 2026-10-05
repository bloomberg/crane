#ifndef INCLUDED_MULTI_ARG_FUNCTION_VALUE
#define INCLUDED_MULTI_ARG_FUNCTION_VALUE

#include "fn.h"
#include <cstdint>
#include <memory>
#include <optional>

/// A function of two or more arguments stored as a *value* is emitted
/// uncurried, function<Nat (Nat, Nat)>, while every slot that holds a
/// function value expects the curried spelling
/// function<function<Nat (Nat)> (Nat)>.  The two never meet: "no viable
/// conversion".  One-argument function values are fine, so this is the
/// currying convention for stored functions, not function storage itself.
struct MultiArgFunctionValue {
  static inline const std::optional<crane::fn<uint64_t(uint64_t, uint64_t)>> o =
      std::make_optional<crane::fn<uint64_t(uint64_t, uint64_t)>>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); });
  static inline const std::optional<crane::fn<uint64_t(uint64_t)>> partial =
      []() {
        return []() -> std::optional<crane::fn<uint64_t(uint64_t)>> {
          if (o.has_value()) {
            const crane::fn<uint64_t(uint64_t, uint64_t)> &f = *o;
            return std::make_optional<crane::fn<uint64_t(uint64_t)>>(
                [=](uint64_t _pa0) { return f(UINT64_C(1), _pa0); });
          } else {
            return std::optional<crane::fn<uint64_t(uint64_t)>>();
          }
        }();
      }();
  static inline const uint64_t run = []() -> uint64_t {
    if (partial.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &g = *partial;
      return g(UINT64_C(2));
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_MULTI_ARG_FUNCTION_VALUE
