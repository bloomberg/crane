#include "pair_closure_escape.h"

uint64_t PairClosureEscape::sum_values(const PairClosureEscape::tree &t,
                                       uint64_t x) {
  if (std::holds_alternative<typename PairClosureEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename PairClosureEscape::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename PairClosureEscape::tree::Leaf>(
            _sv0.v())) {
      return (a1 + x);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename PairClosureEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *a2;
      if (std::holds_alternative<typename PairClosureEscape::tree::Leaf>(
              _sv1.v())) {
        return (a10 + x);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename PairClosureEscape::tree::Node>(_sv1.v());
        return (((a10 + a11) + a1) + x);
      }
    }
  }
}

/// BUG: Partial application stored in fst of a pair (std::make_pair).
/// return_captures_by_value doesn't handle lambdas inside std::make_pair.
std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
PairClosureEscape::pair_escape(PairClosureEscape::tree t) {
  return std::make_pair(
      [=](uint64_t _x0) mutable -> uint64_t { return sum_values(t, _x0); },
      UINT64_C(0));
}

uint64_t PairClosureEscape::use_pair(
    const std::pair<std::function<uint64_t(uint64_t)>, uint64_t> &p) {
  return p.first(p.second);
}
