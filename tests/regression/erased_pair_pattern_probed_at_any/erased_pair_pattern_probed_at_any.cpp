#include "erased_pair_pattern_probed_at_any.h"

pairs<bool, box<bool>> run(const pairs<Nat, box<Nat>> &m) {
  return TFunctor_pairs<TFunctor_box>::template tfmap<Nat, bool>(
      []() {
        auto _pa0 = Nat::s(Nat::s(Nat::s(Nat::o())));
        return [=](Nat _x0) -> bool { return _pa0.ltb(_x0); };
      }(),
      m);
}
