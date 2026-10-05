#include "hk_constraint_carrier_two_params.h"

List<crane::obj> TFunctor_list(const crane::fn<crane::obj(crane::obj)> &x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(x0_);
}

outer1<Nat, two<Nat, List<Nat>>>
HkConstraintCarrierTwoParams::run(const outer1<Nat, two<Nat, List<Nat>>> &m) {
  return tfmap<outer1<crane::obj, two<crane::obj, List<crane::obj>>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0, const auto &_x1)
                   -> outer1<crane::obj, two<crane::obj, List<crane::obj>>> {
          return TFunctor_outer1<List<crane::obj>>(
              [](auto &&_ec0, List<crane::obj> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              []() {
                return
                    [](crane::fn<crane::obj(crane::obj)> _x0,
                       const auto &_x1) -> two<crane::obj, List<crane::obj>> {
                      return TFunctor_two<List<crane::obj>>(
                          [](auto &&_ec0, List<crane::obj> _ec1) {
                            return TFunctor_list(_ec0, _ec1);
                          },
                          _x0,
                          crane_convert<two<crane::obj, List<crane::obj>>>(
                              _x1));
                    };
              }(),
              _x0,
              crane_convert<
                  outer1<crane::obj, two<crane::obj, List<crane::obj>>>>(_x1));
        };
      }(),
      [](const Nat &x) { return Nat::s(x); }, m);
}
