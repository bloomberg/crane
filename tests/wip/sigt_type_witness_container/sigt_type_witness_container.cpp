#include "sigt_type_witness_container.h"

Nat SigtTypeWitnessContainer::depth(const SigT<std::any, std::any> &p) {
  return p.projT2().length();
}
