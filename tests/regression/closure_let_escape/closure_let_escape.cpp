#include "closure_let_escape.h"

/// A local fixpoint captures a LET-BINDING (not a function parameter)
/// and escapes through Some (std::optional).
///
/// BUG: Local fixpoints use & capture. The let-binding base is a
/// stack variable. The fixpoint escapes through Some, so
/// return_captures_by_value does NOT apply. After the function
/// returns, base is destroyed, and the captured reference dangles.
///
/// Difference from fix_escape_capture: captures a LET-BINDING
/// (not a function parameter). The let-binding involves a computation
/// (n * 2), so it can't be optimized away.
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

/// test3: Captures from multiple let bindings.
/// BUG: Both a and b are captured by &, both dangle.
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
