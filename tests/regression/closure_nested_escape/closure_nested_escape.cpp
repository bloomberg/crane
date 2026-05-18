#include "closure_nested_escape.h"

/// A function takes a nat and returns a PAIR of fixpoints, both
/// capturing the same parameter.
///
/// BUG: Both fixpoints use & capture. They capture n by reference.
/// Both are stored in a pair (constructor), so return_captures_by_value
/// does NOT apply. After the function returns, n dangles.
///
/// Difference from fix_escape_capture: returns TWO fixpoints that both
/// capture the SAME variable. This tests whether both closures
/// independently read garbage from the same dangling reference.
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
