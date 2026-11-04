#include "tt_at_computed_type.h"

/// tt returned where the result type is computed by a type-level function.
///
/// tuple (nats n) is unit at 0 and a pair otherwise; erased, it
/// is the box, which holds tt as well as it holds a pair.  The 0 branch
/// of ones is reachable -- every call ends there -- so it must return its
/// tt, not be taken for a branch a dependent match rules out.
List<crane::obj> TtAtComputedType::nats(uint64_t n) {
  if (n <= 0) {
    return List<crane::obj>::nil();
  } else {
    uint64_t m = n - 1;
    return List<crane::obj>::cons(crane::obj(), nats(m));
  }
}

TtAtComputedType::tuple TtAtComputedType::ones(uint64_t n) {
  if (n <= 0) {
    return std::monostate{};
  } else {
    uint64_t m = n - 1;
    return std::make_pair(crane::obj(UINT64_C(1)), crane::obj(ones(m)));
  }
}
