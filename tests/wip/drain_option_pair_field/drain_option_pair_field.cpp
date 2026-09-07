#include "drain_option_pair_field.h"

/// The iterative destructor walks a recursive field to avoid deep recursion.
/// For a field of type option (t * nat) the walk reads the pair component as
/// a0->first, applying operator-> to the std::optional rather than
/// opening it first.  A bare option t and a bare t * t both work, so it is
/// the nesting the drain path does not handle.
uint64_t DrainOptionPairField::depth(const DrainOptionPairField::t &x) {
  const auto &[a0] = std::get<typename DrainOptionPairField::t::C>(x.v());
  if ((*a0).has_value()) {
    const std::pair<DrainOptionPairField::t, uint64_t> &p = *(*a0);
    return (UINT64_C(1) + depth(p.first));
  } else {
    return UINT64_C(0);
  }
}
