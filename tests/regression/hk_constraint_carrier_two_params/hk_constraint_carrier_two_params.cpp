#include "hk_constraint_carrier_two_params.h"

template <typename _CraneTcArg>
using _crane_carrier_tc =
    outer1<_CraneTcArg, two<_CraneTcArg, List<_CraneTcArg>>>;

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

outer1<Nat, two<Nat, List<Nat>>>
HkConstraintCarrierTwoParams::run(const outer1<Nat, two<Nat, List<Nat>>> &m) {
  return tfmap<_crane_carrier_tc>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  outer1<std::any, two<std::any, List<std::any>>> _x1)
                   -> outer1<std::any, two<std::any, List<std::any>>> {
          return TFunctor_outer1<List>(
              [](auto &&_ec0, List<std::any> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              []() {
                return [](std::function<std::any(std::any)> _x0,
                          two<std::any, List<std::any>> _x1)
                           -> two<std::any, List<std::any>> {
                  return TFunctor_two<List>(
                      [](auto &&_ec0, List<std::any> _ec1) {
                        return TFunctor_list(_ec0, _ec1);
                      },
                      _x0, _x1);
                };
              }(),
              _x0, _x1);
        };
      }(),
      [](Nat x) { return Nat::s(x); }, m);
}
