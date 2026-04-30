#include <closure_recursive_build.h>

/// Recursively build a list of fixpoint closures. Each recursive call
/// creates a local fixpoint adder that captures the current n.
///
/// BUG HYPOTHESIS: Each adder captures n from its stack frame
/// by &. The closures are stored in FCons constructors. After
/// build_adders returns, all intermediate stack frames are gone,
/// and every closure holds a dangling reference.
ClosureRecursiveBuild::fn_list
ClosureRecursiveBuild::build_adders(unsigned int n) {
  if (n <= 0) {
    return fn_list::fnil();
  } else {
    unsigned int n_ = n - 1;
    auto adder_impl = [=](auto &_self_adder,
                          unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return n;
      } else {
        unsigned int x_ = x - 1;
        return (_self_adder(_self_adder, x_) + 1);
      }
    };
    auto adder = [=](unsigned int x) mutable -> unsigned int {
      return adder_impl(adder_impl, x);
    };
    return fn_list::fcons(adder, build_adders(n_));
  }
}

unsigned int
ClosureRecursiveBuild::apply_first(const ClosureRecursiveBuild::fn_list &fl,
                                   const unsigned int &x) {
  if (std::holds_alternative<typename ClosureRecursiveBuild::fn_list::FNil>(
          fl.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ClosureRecursiveBuild::fn_list::FCons>(fl.v());
    return d_a0(x);
  }
}

unsigned int
ClosureRecursiveBuild::apply_all_sum(const ClosureRecursiveBuild::fn_list &fl,
                                     const unsigned int &x) {
  if (std::holds_alternative<typename ClosureRecursiveBuild::fn_list::FNil>(
          fl.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ClosureRecursiveBuild::fn_list::FCons>(fl.v());
    return (d_a0(x) + apply_all_sum(*(d_a1), x));
  }
}
