#include "dependent_extraction_targets_b.h"

uint64_t
DependentExtractionTargets::A::get(const DependentExtractionTargets::A::t &x) {
  const auto &[a0] = x;
  return a0;
}
