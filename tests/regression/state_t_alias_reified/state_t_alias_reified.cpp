#include "state_t_alias_reified.h"

template <typename CraneTcArg>
using crane_carrier_tc_609e8855cd7ad294 = std::shared_ptr<ITree<CraneTcArg>>;

Monads::template stateT<uint64_t, crane_carrier_tc_609e8855cd7ad294, uint64_t>
StateTAliasReified::twice(std::type_identity_t<Monads::template stateT<
    uint64_t, crane_carrier_tc_609e8855cd7ad294, uint64_t>> c) {
  return [=, c = std::move(c)](uint64_t s) {
    return itree_bind(c(s), [=, c = c](std::pair<uint64_t, uint64_t> p) {
      return itree_bind(c(p.first), [=](std::pair<uint64_t,
                                                  uint64_t> q) {
                                      return itree_ret(std::make_pair(
                                          q.first, p.second + q.second));
                                    });
    });
  };
}

std::shared_ptr<ITree<std::pair<uint64_t, uint64_t>>>
StateTAliasReified::run(uint64_t n) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto twice_1 = crane::immortal(twice(tick));
  return twice_1(n);
}

StateTAliasReified::M<uint64_t>
StateTAliasReified::plus_one(std::shared_ptr<ITree<uint64_t>> m) {
  return itree_bind(std::move(m),
                    [](uint64_t x) { return itree_ret((x + 1)); });
}

StateTAliasReified::M<uint64_t> StateTAliasReified::seeded(uint64_t n) {
  return itree_bind(seed,
                    [=](uint64_t x) { return plus_one(itree_ret(x + n)); });
}
