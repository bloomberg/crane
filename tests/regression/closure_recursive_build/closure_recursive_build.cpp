#include "closure_recursive_build.h"

/// Recursively build a list of fixpoint closures. Each recursive call
/// creates a local fixpoint adder that captures the current n.
///
/// BUG HYPOTHESIS: Each adder captures n from its stack frame
/// by &. The closures are stored in FCons constructors. After
/// build_adders returns, all intermediate stack frames are gone,
/// and every closure holds a dangling reference.
ClosureRecursiveBuild::fn_list ClosureRecursiveBuild::build_adders(uint64_t n) {
  if (n <= 0) {
    return fn_list::fnil();
  } else {
    uint64_t n_ = n - 1;
    auto adder_impl = [=](auto &_self_adder, uint64_t x) mutable -> uint64_t {
      if (x <= 0) {
        return n;
      } else {
        uint64_t x_ = x - 1;
        return (_self_adder(_self_adder, x_) + 1);
      }
    };
    auto adder = [=](uint64_t x) mutable -> uint64_t {
      return adder_impl(adder_impl, x);
    };
    return fn_list::fcons(adder, build_adders(n_));
  }
}

uint64_t
ClosureRecursiveBuild::apply_first(const ClosureRecursiveBuild::fn_list &fl,
                                   uint64_t x) {
  if (std::holds_alternative<typename ClosureRecursiveBuild::fn_list::FNil>(
          fl.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ClosureRecursiveBuild::fn_list::FCons>(fl.v());
    return a0(x);
  }
}

uint64_t
ClosureRecursiveBuild::apply_all_sum(const ClosureRecursiveBuild::fn_list &fl,
                                     uint64_t x) {
  if (std::holds_alternative<typename ClosureRecursiveBuild::fn_list::FNil>(
          fl.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ClosureRecursiveBuild::fn_list::FCons>(fl.v());
    return (a0(x) + apply_all_sum(*a1, x));
  }
}
