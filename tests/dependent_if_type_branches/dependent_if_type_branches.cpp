#include "dependent_if_type_branches.h"

std::any DependentIfTypeBranches::choose(uint64_t n) {
  if (n == UINT64_C(0)) {
    return UINT64_C(7);
  } else {
    return crane_erase_fn([](uint64_t k) { return (k + UINT64_C(1)); });
  }
}
