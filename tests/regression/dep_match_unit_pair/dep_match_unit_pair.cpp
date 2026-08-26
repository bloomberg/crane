#include "dep_match_unit_pair.h"

std::pair<uint64_t, uint64_t>
DepMatchUnitPair::get(const DepMatchUnitPair::tg &t) {
  if (std::holds_alternative<typename DepMatchUnitPair::tg::TP>(t.v())) {
    const auto &[a0, a1] = std::get<typename DepMatchUnitPair::tg::TP>(t.v());
    return std::make_pair(a0, a1);
  } else {
    throw std::logic_error("unreachable: impossible dependent match branch");
  }
}
