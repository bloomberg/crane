#include <option_some_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
OptionSomeEscape::sum_values(const std::shared_ptr<OptionSomeEscape::tree> &t,
                             const unsigned int x) {
  return std::visit(
      Overloaded{
          [&](const typename OptionSomeEscape::tree::Leaf _args)
              -> unsigned int { return std::move(x); },
          [&](const typename OptionSomeEscape::tree::Node _args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename OptionSomeEscape::tree::Leaf _args0)
                        -> unsigned int { return (_args.d_a1 + std::move(x)); },
                    [&](const typename OptionSomeEscape::tree::Node _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename OptionSomeEscape::tree::Leaf
                                      _args1) -> unsigned int {
                                return (_args0.d_a1 + std::move(x));
                              },
                              [&](const typename OptionSomeEscape::tree::Node
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

/// BUG: Partial application stored in Some (std::make_optional).
/// The & lambda captures parameter t by reference.
/// return_captures_by_value doesn't handle lambdas inside
/// std::make_optional. When the function returns, t is destroyed.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
OptionSomeEscape::option_escape(std::shared_ptr<OptionSomeEscape::tree> t) {
  return std::make_optional<std::function<unsigned int(unsigned int)>>(
      [&](unsigned int _x0) -> unsigned int { return sum_values(t, _x0); });
}

__attribute__((pure)) unsigned int OptionSomeEscape::apply_option(
    const std::optional<std::function<unsigned int(unsigned int)>> o,
    const unsigned int x) {
  if (o.has_value()) {
    std::function<unsigned int(unsigned int)> f = *o;
    return std::move(f)(x);
  } else {
    return std::move(x);
  }
}
