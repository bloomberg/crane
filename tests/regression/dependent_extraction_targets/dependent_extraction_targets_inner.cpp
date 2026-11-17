#include "dependent_extraction_targets_inner.h"

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
