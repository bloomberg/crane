// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <pair_abstract_components_by_reference.h>
#include <cassert>
#include <type_traits>

using M = PairAbstractComponentsByReference;

// A pair or option of functor-abstract components is lent by const
// reference; a pair of free-to-copy components is passed by value.
static_assert(std::is_same_v<decltype(&M::P::compare),
                             Comparison (*)(const M::P::t &, const M::P::t &)>);
static_assert(std::is_same_v<decltype(&M::P::eqb),
                             bool (*)(const M::P::t &, const M::P::t &)>);
static_assert(std::is_same_v<decltype(&M::O::compare),
                             Comparison (*)(const M::O::t &, const M::O::t &)>);
static_assert(std::is_same_v<decltype(&M::sum_pair),
                             uint64_t (*)(std::pair<uint64_t, uint64_t>)>);

int main() {
  assert(M::test_pair == Comparison::LT);
  assert(M::test_opt == Comparison::LT);
  M::P::t p{List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()), 7};
  assert(M::P::eqb(p, p));
  assert(M::sum_pair({2, 3}) == 5);
  return 0;
}
