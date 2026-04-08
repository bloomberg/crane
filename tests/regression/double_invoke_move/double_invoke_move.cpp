#include <double_invoke_move.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// wrap_with takes TWO args. Partial application creates a closure.
/// Since t is stored in a constructor, wrap_with takes t as owned (by value).
std::shared_ptr<DoubleInvokeMove::tree>
DoubleInvokeMove::wrap_with(std::shared_ptr<DoubleInvokeMove::tree> t,
                            const unsigned int v) {
  return tree::node(t, v, tree::leaf());
}

__attribute__((pure)) unsigned int
DoubleInvokeMove::left_value(const std::shared_ptr<DoubleInvokeMove::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename DoubleInvokeMove::tree::Leaf _args)
              -> unsigned int { return 0u; },
          [](const typename DoubleInvokeMove::tree::Node _args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [](const typename DoubleInvokeMove::tree::Leaf _args0)
                        -> unsigned int { return 0u; },
                    [](const typename DoubleInvokeMove::tree::Node _args0)
                        -> unsigned int { return _args0.d_a1; }},
                _args.d_a0->v());
          }},
      t->v());
}
