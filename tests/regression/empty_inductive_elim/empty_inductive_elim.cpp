#include "empty_inductive_elim.h"

/// Eliminating an inductive with no constructors is unreachable, and Crane
/// emits []() { throw std::logic_error("absurd case"); }() for it.  That
/// lambda's deduced return type is void, so it cannot initialise the value
/// the elimination is supposed to produce.
uint64_t EmptyInductiveElim::absurd() { throw std::logic_error("absurd case"); }

uint64_t EmptyInductiveElim::g(const std::optional<std::any> &o) {
  if (o.has_value()) {
    const std::any &_x = *o;
    return absurd();
  } else {
    return UINT64_C(0);
  }
}
