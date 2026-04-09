#include <hof_closure_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
HofClosureEscape::sum_values(const std::shared_ptr<HofClosureEscape::tree> &t,
                             const unsigned int x) {
  return std::visit(
      Overloaded{
          [&](const typename HofClosureEscape::tree::Leaf _args)
              -> unsigned int { return std::move(x); },
          [&](const typename HofClosureEscape::tree::Node _args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename HofClosureEscape::tree::Leaf _args0)
                        -> unsigned int { return (_args.d_a1 + std::move(x)); },
                    [&](const typename HofClosureEscape::tree::Node _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename HofClosureEscape::tree::Leaf
                                      _args1) -> unsigned int {
                                return (_args0.d_a1 + std::move(x));
                              },
                              [&](const typename HofClosureEscape::tree::Node
                                      _args1) -> unsigned int {
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

/// BUG: The partial application sum_values t creates a & lambda.
/// Even though wrap_some just passes f through to Some,
/// the & lambda was created in hof_escape's stack frame.
/// When hof_escape returns, captured t is destroyed.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
HofClosureEscape::hof_escape(std::shared_ptr<HofClosureEscape::tree> t) {
  return wrap_some([=](unsigned int _x0) mutable -> unsigned int {
    return sum_values(t, _x0);
  });
}

__attribute__((pure)) unsigned int HofClosureEscape::apply_option(
    const std::optional<std::function<unsigned int(unsigned int)>> o,
    const unsigned int x) {
  if (o.has_value()) {
    std::function<unsigned int(unsigned int)> f = *o;
    return std::move(f)(x);
  } else {
    return std::move(x);
  }
}
