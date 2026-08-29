#include "dep_match_unit_option.h"

std::optional<uint64_t>
DepMatchUnitOption::get(const DepMatchUnitOption::tg &t) {
  if (std::holds_alternative<typename DepMatchUnitOption::tg::TO>(t.v())) {
    const auto &[a0] = std::get<typename DepMatchUnitOption::tg::TO>(t.v());
    return a0;
  } else {
    throw std::logic_error("unreachable: impossible dependent match branch");
  }
}
