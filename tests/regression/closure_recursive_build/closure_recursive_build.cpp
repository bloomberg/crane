#include <closure_recursive_build.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Recursively build a list of fixpoint closures. Each recursive call
/// creates a local fixpoint adder that captures the current n.
///
/// BUG HYPOTHESIS: Each adder captures n from its stack frame
/// by &. The closures are stored in FCons constructors. After
/// build_adders returns, all intermediate stack frames are gone,
/// and every closure holds a dangling reference.
__attribute__((pure)) ClosureRecursiveBuild::fn_list
ClosureRecursiveBuild::build_adders(unsigned int n) {
  if (n <= 0) {
    return fn_list::fnil();
  } else {
    unsigned int n_ = n - 1;
    auto adder = std::make_shared<std::function<unsigned int(unsigned int)>>();
    *adder = [=](unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return n;
      } else {
        unsigned int x_ = x - 1;
        return ((*adder)(x_) + 1);
      }
    };
    return fn_list::fcons((*adder), build_adders(n_));
  }
}

__attribute__((pure)) unsigned int
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

__attribute__((pure)) unsigned int
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
