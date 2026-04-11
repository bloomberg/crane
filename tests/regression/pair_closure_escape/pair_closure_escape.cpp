#include <pair_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
PairClosureEscape::sum_values(const std::shared_ptr<PairClosureEscape::tree> &t,
                              const unsigned int x) {
  return std::visit(
      Overloaded{
          [&](const typename PairClosureEscape::tree::Leaf _args)
              -> unsigned int { return x; },
          [&](const typename PairClosureEscape::tree::Node _args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename PairClosureEscape::tree::Leaf _args0)
                        -> unsigned int { return (_args.d_a1 + x); },
                    [&](const typename PairClosureEscape::tree::Node _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename PairClosureEscape::tree::Leaf
                                      _args1) -> unsigned int {
                                return (_args0.d_a1 + x);
                              },
                              [&](const typename PairClosureEscape::tree::Node
                                      _args1) -> unsigned int {
                                return (
                                    ((_args0.d_a1 + _args1.d_a1) + _args.d_a1) +
                                    x);
                              }},
                          _args.d_a2->v());
                    }},
                _args.d_a0->v());
          }},
      t->v());
}

/// BUG: Partial application stored in fst of a pair (std::make_pair).
/// return_captures_by_value doesn't handle lambdas inside std::make_pair.
__attribute__((pure))
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
PairClosureEscape::pair_escape(std::shared_ptr<PairClosureEscape::tree> t) {
  return std::make_pair(
      [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      },
      0u);
}

__attribute__((pure)) unsigned int PairClosureEscape::use_pair(
    const std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
        p) {
  return p.first(p.second);
}
