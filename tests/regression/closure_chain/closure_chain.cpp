#include <closure_chain.h>

unsigned int ClosureChain::tree_sum(const ClosureChain::tree &t) {
  if (std::holds_alternative<typename ClosureChain::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ClosureChain::tree::Node>(t.v());
    return ((tree_sum(*(d_a0)) + d_a1) + tree_sum(*(d_a2)));
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
unsigned int ClosureChain::make_chain(const unsigned int &n,
                                      const ClosureChain::tree &t,
                                      unsigned int _x0) {
  return [=]() mutable -> std::function<unsigned int(unsigned int)> {
    if (n <= 0) {
      return [=](const unsigned int &x) mutable { return (tree_sum(t) + x); };
    } else {
      unsigned int n_ = n - 1;
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return make_chain(n_, t, _x0);
      };
      return [=](const unsigned int &x) mutable { return f((x + 1u)); };
    }
  }()(_x0);
}
