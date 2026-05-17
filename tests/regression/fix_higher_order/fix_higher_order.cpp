#include "fix_higher_order.h"

/// Creates a fixpoint and passes it through wrap_fn.
/// The fixpoint escapes through the function call, not through
/// direct constructor application.
///
/// BUG HYPOTHESIS: When the fixpoint is passed as an argument to
/// wrap_fn, the translation may use & capture. wrap_fn stores
/// it in Some and returns. After make_wrapped returns, the
/// captured base is destroyed.
std::optional<std::function<uint64_t(uint64_t)>>
FixHigherOrder::make_wrapped(uint64_t base) {
  auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](uint64_t x) mutable -> uint64_t { return go_impl(go_impl, x); };
  return wrap_fn(go);
}

std::optional<std::optional<std::function<uint64_t(uint64_t)>>>
FixHigherOrder::make_double_wrapped(uint64_t base) {
  auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](uint64_t x) mutable -> uint64_t { return go_impl(go_impl, x); };
  return double_wrap(go);
}
