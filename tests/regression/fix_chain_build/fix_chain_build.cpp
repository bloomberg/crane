#include "fix_chain_build.h"

/// Recursive construction of a closure chain. Each level creates a
/// local fixpoint that captures the current n AND the previous
/// level's closure prev, then stores the fixpoint in a pair with
/// its base value (preventing uncurrying).
///
/// BUG: Each step fixpoint uses & capture, binding n (the
/// current stack frame's parameter), prev (a local variable),
/// and step itself. When build_chain returns, the stack frame
/// is destroyed, and the returned closure holds dangling references.
std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
FixChainBuild::build_chain(uint64_t n) {
  if (n <= 0) {
    return std::make_pair(UINT64_C(0), [](uint64_t x) { return x; });
  } else {
    uint64_t n_ = n - 1;
    auto _cs = build_chain(n_);
    const uint64_t &_x = _cs.first;
    const std::function<uint64_t(uint64_t)> &prev = _cs.second;
    auto step_impl = [=](auto &_self_step, uint64_t x) mutable -> uint64_t {
      if (x <= 0) {
        return n;
      } else {
        uint64_t x_ = x - 1;
        return (prev(_self_step(_self_step, x_)) + 1);
      }
    };
    auto step = [=](uint64_t x) mutable -> uint64_t {
      return step_impl(step_impl, x);
    };
    return std::make_pair(std::move(n), step);
  }
}
