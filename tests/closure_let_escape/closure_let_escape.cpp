#include "closure_let_escape.h"

std::optional<std::function<uint64_t(uint64_t)>>
ClosureLetEscape::make_fn_fix(uint64_t n) {
  uint64_t base = (n * UINT64_C(2));
  auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (_self_add(_self_add, x_) + 1);
    }
  };
  auto add = [=](uint64_t x) mutable -> uint64_t {
    return add_impl(add_impl, x);
  };
  return std::make_optional<std::function<uint64_t(uint64_t)>>(add);
}

std::optional<std::function<uint64_t(uint64_t)>>
ClosureLetEscape::make_fn_multi(uint64_t n) {
  uint64_t a = (n + UINT64_C(1));
  uint64_t b = (a * UINT64_C(3));
  auto helper_impl = [=](auto &_self_helper, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return (a + b);
    } else {
      uint64_t x_ = x - 1;
      return (_self_helper(_self_helper, x_) + 1);
    }
  };
  auto helper = [=](uint64_t x) mutable -> uint64_t {
    return helper_impl(helper_impl, x);
  };
  return std::make_optional<std::function<uint64_t(uint64_t)>>(helper);
}
