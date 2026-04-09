#include <partial_app_move.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A function taking two args: tree -> nat -> nat.
/// Partial application of this to a tree creates a
/// closure nat -> nat in C++ via & lambda.
__attribute__((pure)) unsigned int
PartialAppMove::sum_values(const std::shared_ptr<PartialAppMove::tree> &t,
                           const unsigned int x) {
  return std::visit(
      Overloaded{
          [&](const typename PartialAppMove::tree::Leaf _args) -> auto {
            return std::move(x);
          },
          [&](const typename PartialAppMove::tree::Node _args) -> auto {
            return std::visit(
                Overloaded{
                    [&](const typename PartialAppMove::tree::Leaf _args0)
                        -> auto { return (_args.d_a1 + std::move(x)); },
                    [&](const typename PartialAppMove::tree::Node _args0)
                        -> auto {
                      return std::visit(
                          Overloaded{
                              [&](const typename PartialAppMove::tree::Leaf
                                      _args1) -> auto {
                                return (_args0.d_a1 + std::move(x));
                              },
                              [&](const typename PartialAppMove::tree::Node
                                      _args1) -> auto {
                                return (
                                    ((_args0.d_a1 + _args1.d_a1) + _args.d_a1) +
                                    std::move(x));
                              }},
                          _args.d_a2->v());
                    }},
                _args.d_a0->v());
          }},
      t->v());
}

/// Wrap a tree inside another Node.
/// In C++, this calls tree::node() which has rvalue ref overloads.
/// If escape analysis adds std::move(t) here, the move is REAL.
std::shared_ptr<PartialAppMove::tree>
PartialAppMove::wrap(std::shared_ptr<PartialAppMove::tree> t) {
  return tree::node(t, 0u, tree::leaf());
}

/// BUG TRIGGER: partial application creates a & lambda capturing t,
/// then t is passed to a constructor (actually moved via rvalue ref),
/// then the lambda accesses the moved-from t.
__attribute__((pure)) unsigned int
PartialAppMove::trigger_bug(std::shared_ptr<PartialAppMove::tree> t) {
  std::function<unsigned int(unsigned int)> f =
      [=](unsigned int _x0) mutable -> unsigned int {
    return sum_values(t, _x0);
  };
  std::shared_ptr<PartialAppMove::tree> w = wrap(std::move(t));
  return std::visit(
      Overloaded{
          [&](const typename PartialAppMove::tree::Leaf _args) -> unsigned int {
            return f(0u);
          },
          [&](const typename PartialAppMove::tree::Node _args) -> unsigned int {
            return f(99u);
          }},
      w->v());
}
