#include "fix_capture_fn_arg.h"

/// A local fixpoint captures a FUNCTION argument AND is returned
/// through a pair (preventing uncurrying).
///
/// BUG: go uses & capture. Both f (a std::function on the
/// caller's stack) and base are captured by reference.
/// The fixpoint escapes through the pair — after make_transform
/// returns, f (the std::function object), base, and the local
/// go are all destroyed. The returned closure dereferences a
/// destroyed std::function when it calls f.
std::pair<uint64_t, crane::fn<uint64_t(uint64_t)>>
FixCaptureFnArg::make_transform(crane::fn<uint64_t(uint64_t)> f,
                                uint64_t base) {
  auto go_impl = [=](auto &_self_go, uint64_t x) -> uint64_t {
    if (x <= 0) {
      return f(base);
    } else {
      uint64_t x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go =
      [=, go_impl = std::move(go_impl)](uint64_t x) -> uint64_t {
        return go_impl(go_impl, x);
      };
  return std::make_pair(f(base), std::move(go));
}
