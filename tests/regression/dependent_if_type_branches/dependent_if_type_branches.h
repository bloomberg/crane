#ifndef INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
#define INCLUDED_DEPENDENT_IF_TYPE_BRANCHES

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>

/// A definition whose return type is a dependent if computing nat in one
/// branch and nat -> nat in the other erases to std::any: the returned
/// closure is stored through the canonical adapter and the application site
/// casts it back.
struct DependentIfTypeBranches {
  static crane::obj choose(uint64_t n);
  static constexpr uint64_t go = UINT64_C(49);
};

#endif // INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
