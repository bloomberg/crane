#include "dependent_if_type_branches.h"

/// WIP: A definition whose return type is an `if` over a boolean computing
/// `nat` in one branch and `nat -> nat` in the other erases to `std::any`,
/// which is then applied as a function.
std::any DependentIfTypeBranches::choose(uint64_t n) {
  if (n == UINT64_C(0)) {
    return UINT64_C(7);
  } else {
    return [](uint64_t k) { return (k + UINT64_C(1)); };
  }
}
