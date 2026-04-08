#include <closure_chain.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ClosureChain::tree_sum(const std::shared_ptr<ClosureChain::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename ClosureChain::tree::Leaf _args) -> unsigned int {
            return 0u;
          },
          [](const typename ClosureChain::tree::Node _args) -> unsigned int {
            return ((tree_sum(_args.d_a0) + _args.d_a1) + tree_sum(_args.d_a2));
          }},
      t->v());
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
__attribute__((pure)) unsigned int
ClosureChain::make_chain(const unsigned int n,
                         const std::shared_ptr<ClosureChain::tree> &t,
                         const unsigned int _x0) {
  return [&]() -> std::function<unsigned int(unsigned int)> {
    if (n <= 0) {
      return [=](unsigned int x) mutable { return (tree_sum(t) + x); };
    } else {
      unsigned int n_ = n - 1;
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return make_chain(n_, t, _x0);
      };
      return [=](unsigned int x) mutable { return f((x + 1u)); };
    }
  }()(std::move(_x0));
}
