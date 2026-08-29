#include "pair_both_recursive.h"

PairBothRecursive::t PairBothRecursive::wrap(PairBothRecursive::t acc) {
  return t::br(std::make_pair(std::move(acc), t::leaf(UINT64_C(0))));
}

uint64_t PairBothRecursive::size(const PairBothRecursive::t &x) {
  if (std::holds_alternative<typename PairBothRecursive::t::Leaf>(x.v())) {
    return UINT64_C(1);
  } else {
    const auto &[a0] = std::get<typename PairBothRecursive::t::Br>(x.v());
    const auto &[a, b] = (*a0);
    return (size(a) + size(b));
  }
}
