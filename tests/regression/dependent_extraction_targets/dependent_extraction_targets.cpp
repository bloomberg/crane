#include "dependent_extraction_targets.h"

uint64_t DependentExtractionTargets::Inner::f(
    const DependentExtractionTargets::Inner::t &x) {
  if (std::holds_alternative<typename DependentExtractionTargets::Inner::t::A>(
          x.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] =
        std::get<typename DependentExtractionTargets::Inner::t::B>(x.v());
    return a0;
  }
}

uint64_t
DependentExtractionTargets::A::get(const DependentExtractionTargets::A::t &x) {
  const auto &[a0] = x;
  return a0;
}
