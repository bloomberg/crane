#include "assoc_pair_list.h"

AssocPairList::t AssocPairList::wrap(uint64_t k, AssocPairList::t acc) {
  return t::node(List<std::pair<uint64_t, AssocPairList::t>>::cons(
      std::make_pair(k, std::move(acc)),
      List<std::pair<uint64_t, AssocPairList::t>>::nil()));
}

uint64_t AssocPairList::count(const AssocPairList::t &x) {
  const auto &[a0] = std::get<typename AssocPairList::t::Node>(x.v());
  const List<std::pair<uint64_t, AssocPairList::t>> &a0_value = *a0;
  return (a0_value.template fold_left<uint64_t>(
              [](uint64_t a, const std::pair<uint64_t, AssocPairList::t> &p) {
                return (a + count(p.second));
              },
              UINT64_C(0)) +
          1);
}
