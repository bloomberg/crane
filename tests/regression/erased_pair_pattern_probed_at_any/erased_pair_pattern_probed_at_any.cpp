#include "erased_pair_pattern_probed_at_any.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = pairs<_CraneTcArg, box<_CraneTcArg>>;

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b) {
  return box<std::any>{f(b.b_payload)};
}

pairs<bool, box<bool>> run(const pairs<Nat, box<Nat>> &m) {
  return tfmap<_crane_carrier_tc>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  pairs<std::any, std::any> _x1) -> pairs<std::any, std::any> {
          return TFunctor_pairs<box>(
              [](auto &&_ec0, box<std::any> _ec1) {
                return TFunctor_box(_ec0, _ec1);
              },
              _x0, _x1);
        };
      }(),
      [](Nat _x0) -> bool { return Nat::s(Nat::s(Nat::s(Nat::o()))).ltb(_x0); },
      m);
}
