#include "dependent_if_type_branches.h"

/// A definition whose return type is a dependent if computing nat in one
/// branch and nat -> nat in the other erases to std::any: the returned
/// closure is stored through the canonical adapter and the application site
/// casts it back.
std::any DependentIfTypeBranches::choose(uint64_t n) {
  if (n == UINT64_C(0)) {
    return UINT64_C(7);
  } else {
    return crane_erase_fn([](uint64_t k) { return (k + UINT64_C(1)); });
  }
}
