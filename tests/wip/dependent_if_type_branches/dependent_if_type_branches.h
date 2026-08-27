#ifndef INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
#define INCLUDED_DEPENDENT_IF_TYPE_BRANCHES

#include <any>

/// WIP: A definition whose return type is an `if` over a boolean computing
/// `nat` in one branch and `nat -> nat` in the other erases to `std::any`,
/// which is then applied as a function.
struct DependentIfTypeBranches {
  static std::any choose(uint64_t n);
  static inline const uint64_t go =
      (choose(UINT64_C(1))(UINT64_C(41)) +
       std::any_cast<uint64_t>(choose(UINT64_C(0))));
};

#endif // INCLUDED_DEPENDENT_IF_TYPE_BRANCHES
