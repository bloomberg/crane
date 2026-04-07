#include <option_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int OptionClosureEscape::sum_values(
    const std::shared_ptr<OptionClosureEscape::tree> &t, const unsigned int x) {
  return std::visit(
      Overloaded{
          [&](const typename OptionClosureEscape::tree::Leaf _args)
              -> unsigned int { return std::move(x); },
          [&](const typename OptionClosureEscape::tree::Node _args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename OptionClosureEscape::tree::Leaf _args0)
                        -> unsigned int { return (_args.d_a1 + std::move(x)); },
                    [&](const typename OptionClosureEscape::tree::Node _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename OptionClosureEscape::tree::Leaf
                                      _args1) -> unsigned int {
                                return (_args0.d_a1 + std::move(x));
                              },
                              [&](const typename OptionClosureEscape::tree::Node
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

/// BUG: pair_escape stores a & lambda in a pair.
/// The lambda captures parameter t by reference.
/// When pair_escape returns, t is destroyed → dangling.
__attribute__((pure))
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
OptionClosureEscape::pair_escape(std::shared_ptr<OptionClosureEscape::tree> t) {
  return std::make_pair(
      [&](unsigned int _x0) -> unsigned int { return sum_values(t, _x0); },
      42u);
}

/// BUG: match_pair — & captures _args from visit scope.
__attribute__((pure))
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
OptionClosureEscape::match_pair(
    const std::shared_ptr<OptionClosureEscape::tree> &t) {
  return std::visit(
      Overloaded{[](const typename OptionClosureEscape::tree::Leaf _args)
                     -> std::pair<std::function<unsigned int(unsigned int)>,
                                  unsigned int> {
                   return std::make_pair([](unsigned int x) { return x; }, 0u);
                 },
                 [](const typename OptionClosureEscape::tree::Node _args)
                     -> std::pair<std::function<unsigned int(unsigned int)>,
                                  unsigned int> {
                   return std::make_pair(
                       [&](unsigned int _x0) -> unsigned int {
                         return sum_values(_args.d_a0, _x0);
                       },
                       _args.d_a1);
                 }},
      t->v());
}
