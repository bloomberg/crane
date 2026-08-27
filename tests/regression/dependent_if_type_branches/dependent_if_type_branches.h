#ifndef INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
#define INCLUDED_DEPENDENT_IF_TYPE_BRANCHES

#include "crane_fn.h"
#include <any>
#include <functional>

/// A definition whose return type is a dependent if computing nat in one
/// branch and nat -> nat in the other erases to std::any: the returned
/// closure is stored through the canonical adapter and the application site
/// casts it back.
struct DependentIfTypeBranches {
  static std::any choose(uint64_t n);
  static inline const uint64_t go =
      (std::any_cast<uint64_t>(std::any_cast<std::function<std::any(std::any)>>(
           choose(UINT64_C(1)))(std::any(UINT64_C(41)))) +
       std::any_cast<uint64_t>(choose(UINT64_C(0))));
};

#endif // INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
