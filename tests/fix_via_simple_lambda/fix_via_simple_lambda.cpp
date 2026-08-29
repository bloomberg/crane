#include "fix_via_simple_lambda.h"

std::optional<std::function<uint64_t(uint64_t)>>
FixViaSimpleLambda::make_combined(uint64_t n) {
  uint64_t base = (n * UINT64_C(2));
  auto double_add_impl = [=](auto &_self_double_add,
                             uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (UINT64_C(2) + _self_double_add(_self_double_add, x_));
    }
  };
  auto double_add = [=](uint64_t x) mutable -> uint64_t {
    return double_add_impl(double_add_impl, x);
  };
  auto triple_add_impl = [=](auto &_self_triple_add,
                             uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (UINT64_C(3) + _self_triple_add(_self_triple_add, x_));
    }
  };
  auto triple_add = [=](uint64_t x) mutable -> uint64_t {
    return triple_add_impl(triple_add_impl, x);
  };
  return std::make_optional<std::function<uint64_t(uint64_t)>>(
      [=](uint64_t x) mutable { return (double_add(x) + triple_add(x)); });
}
