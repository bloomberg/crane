#include "higher_rank_poly.h"

/// A rank-2 argument: f is polymorphic and gets used at two different types.
/// Crane emits the two results without casting them back from std::any, and
/// emits a bogus body for the identity lambda passed in.
std::pair<Nat, bool>
HigherRankPoly::apply_id(const crane::fn<crane::obj(crane::obj)> &f) {
  return std::make_pair(crane::any_cast<Nat>(f(Nat::s(Nat::o()))),
                        crane::any_cast<bool>(f(true)));
}
