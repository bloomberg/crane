#include "superclass_only_concept.h"

uint64_t SuperclassOnlyConcept::run(uint64_t k) {
  return go<SuperclassOnlyConcept::BothN, uint64_t>((k + UINT64_C(1)));
}
