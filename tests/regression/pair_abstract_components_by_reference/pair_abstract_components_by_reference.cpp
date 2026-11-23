#include "pair_abstract_components_by_reference.h"

Comparison PairAbstractComponentsByReference::NatListCmp::compare(
    const List<uint64_t> &x, const List<uint64_t> &y) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(x.v())) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(y.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(x.v());
    if (std::holds_alternative<typename List<uint64_t>::Nil>(y.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(y.v());
      switch ((a0 < a00 ? Comparison::LT
                        : (a00 < a0 ? Comparison::GT : Comparison::EQ))) {
      case Comparison::EQ: {
        return compare(*a1, *a10);
      }
      case Comparison::LT: {
        return Comparison::LT;
      }
      case Comparison::GT: {
        return Comparison::GT;
      }
      default:
        std::unreachable();
      }
    }
  }
}

Comparison PairAbstractComponentsByReference::NatCmp::compare(uint64_t x0_,
                                                              uint64_t x1_) {
  return (x0_ < x1_ ? Comparison::LT
                    : (x1_ < x0_ ? Comparison::GT : Comparison::EQ));
}

uint64_t
PairAbstractComponentsByReference::sum_pair(std::pair<uint64_t, uint64_t> p) {
  const auto &[a, b] = p;
  return (a + b);
}
