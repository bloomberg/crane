#include "dep_match_unit_vec.h"

uint64_t DepMatchUnitVec::head(uint64_t,
                               const DepMatchUnitVec::vec<uint64_t> &v) {
  if (std::holds_alternative<typename DepMatchUnitVec::vec<uint64_t>::Vnil>(
          v.v())) {
    throw std::logic_error("unreachable: impossible dependent match branch");
  } else {
    const auto &[n, a1, a2] =
        std::get<typename DepMatchUnitVec::vec<uint64_t>::Vcons>(v.v());
    return a1;
  }
}
