#include "partial_application.h"

std::pair<bool, Box<bool>>
PartialApplication::convert(const std::pair<Nat, Box<Nat>> &p) {
  return TFunctor_pair<TFunctor_box<Endo_id<Nat>>>::template tfmap<Nat, bool>(
      [](const Nat &n) { return n.eqb(Nat::o()); }, p);
}
