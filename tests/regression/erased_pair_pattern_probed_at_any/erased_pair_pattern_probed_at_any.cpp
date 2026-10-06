#include "erased_pair_pattern_probed_at_any.h"

pairs<bool, box<bool>> run(const pairs<Nat, box<Nat>> &m) {
  return TFunctor_pairs<TFunctor_box>::template tfmap<Nat, bool>(
      [](Nat _x0) -> bool { return Nat::s(Nat::s(Nat::s(Nat::o()))).ltb(_x0); },
      m);
}
