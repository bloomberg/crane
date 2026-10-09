#ifndef INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
#define INCLUDED_DEPENDENT_IF_TYPE_BRANCHES

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <cstdint>
#include <functional>

/// A definition whose return type is a dependent if computing nat in one
/// branch and nat -> nat in the other erases to std::any: the returned
/// closure is stored through the canonical adapter and the application site
/// casts it back.
struct DependentIfTypeBranches {
  static crane::obj choose(uint64_t n);
  static inline const uint64_t go =
      (crane::any_cast<uint64_t>(
           crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
               choose(UINT64_C(1)))(crane::obj(UINT64_C(41)))) +
       crane::any_cast<uint64_t>(choose(UINT64_C(0))));
};

#endif // INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
