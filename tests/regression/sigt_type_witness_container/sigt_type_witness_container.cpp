#include "sigt_type_witness_container.h"

Nat SigtTypeWitnessContainer::depth(
    const SigT<crane::obj, List<crane::obj>> &p) {
  return crane::any_cast<List<crane::obj>>(p.projT2()).length();
}
