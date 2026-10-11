#include "persistent_array_default_construction.h"

uint64_t PersistentArrayDefaultConstruction::get0(
    const PersistentArrayDefaultConstruction::t &x) {
  if (std::holds_alternative<
          typename PersistentArrayDefaultConstruction::t::T0>(x.v())) {
    const auto &[a0] =
        std::get<typename PersistentArrayDefaultConstruction::t::T0>(x.v());
    return a0.get(INT64_C(0));
  } else {
    return UINT64_C(0);
  }
}
