#include <pair_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
PairClosureEscape::sum_values(const std::shared_ptr<PairClosureEscape::tree> &t,
                              const unsigned int x) {
  if (std::holds_alternative<typename PairClosureEscape::tree::Leaf>(t->v())) {
    return x;
  } else {
    const auto &_m =
        *std::get_if<typename PairClosureEscape::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename PairClosureEscape::tree::Leaf>(
            _sv0->v())) {
      return (_m.d_a1 + x);
    } else {
      const auto &_m0 =
          *std::get_if<typename PairClosureEscape::tree::Node>(&_sv0->v());
      auto &&_sv1 = _m.d_a2;
      if (std::holds_alternative<typename PairClosureEscape::tree::Leaf>(
              _sv1->v())) {
        return (_m0.d_a1 + x);
      } else {
        const auto &_m1 =
            *std::get_if<typename PairClosureEscape::tree::Node>(&_sv1->v());
        return (((_m0.d_a1 + _m1.d_a1) + _m.d_a1) + x);
      }
    }
  }
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
