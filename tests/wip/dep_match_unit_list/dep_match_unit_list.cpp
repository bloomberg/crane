#include "dep_match_unit_list.h"

List<uint64_t> DepMatchUnitList::get(const DepMatchUnitList::tg &t) {
  if (std::holds_alternative<typename DepMatchUnitList::tg::TL>(t.v())) {
    const auto &[a0] = std::get<typename DepMatchUnitList::tg::TL>(t.v());
    return a0;
  } else {
    return std::monostate{};
  }
}
