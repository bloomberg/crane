#include "dep_match_unit_bool_idx.h"

uint64_t DepMatchUnitBoolIdx::get(const DepMatchUnitBoolIdx::tagged &t) {
  if (std::holds_alternative<typename DepMatchUnitBoolIdx::tagged::TA>(t.v())) {
    const auto &[a0] =
        std::get<typename DepMatchUnitBoolIdx::tagged::TA>(t.v());
    return a0;
  } else {
    throw std::logic_error("unreachable: impossible dependent match branch");
  }
}
