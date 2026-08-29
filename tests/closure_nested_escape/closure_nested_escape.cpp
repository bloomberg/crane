#include "closure_nested_escape.h"

std::pair<std::function<uint64_t(uint64_t)>, std::function<uint64_t(uint64_t)>>
ClosureNestedEscape::make_pair_fix(uint64_t n) {
  auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return n;
    } else {
      uint64_t x_ = x - 1;
      return (_self_add(_self_add, x_) + 1);
    }
  };
  auto add = [=](uint64_t x) mutable -> uint64_t {
    return add_impl(add_impl, x);
  };
  auto mul_impl = [=](auto &_self_mul, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t x_ = x - 1;
      return (n + _self_mul(_self_mul, x_));
    }
  };
  auto mul = [=](uint64_t x) mutable -> uint64_t {
    return mul_impl(mul_impl, x);
  };
  return std::make_pair(add, mul);
}
