#include "closure_chain.h"

uint64_t ClosureChain::tree_sum(const ClosureChain::tree &t) {
  if (std::holds_alternative<typename ClosureChain::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename ClosureChain::tree::Node>(t.v());
    return ((tree_sum(*a0) + a1) + tree_sum(*a2));
  }
}

/// Build a chain of closures via recursion.
/// Each level wraps the previous closure in a new one.
///
/// make_chain 0 t = fun x => tree_sum t + x
/// make_chain 1 t = fun x => (fun x => tree_sum t + x) (x + 1)
/// make_chain n t = fun x => (make_chain (n-1) t) (x + 1)
///
/// BUG HYPOTHESIS: make_chain (S n') t creates a local binding
/// f := make_chain n' t, then returns fun x => f (x + 1).
/// If f is captured by &, it dies when make_chain returns.
uint64_t ClosureChain::make_chain(uint64_t n, const ClosureChain::tree &t,
                                  uint64_t _x0) {
  return [=]() mutable -> std::function<uint64_t(uint64_t)> {
    if (n <= 0) {
      return [=](uint64_t x) mutable { return (tree_sum(t) + x); };
    } else {
      uint64_t n_ = n - 1;
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return make_chain(n_, t, _x0);
      };
      return [=](uint64_t x) mutable { return f((x + UINT64_C(1))); };
    }
  }()(_x0);
}
