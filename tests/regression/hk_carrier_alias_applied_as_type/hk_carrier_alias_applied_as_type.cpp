#include "hk_carrier_alias_applied_as_type.h"

List<crane::obj> TFunctor_list(const crane::fn<crane::obj(crane::obj)> &x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(x0_);
}

modul<Nat, List<Nat>>
HkCarrierAliasAppliedAsType::run(const modul<Nat, List<Nat>> &m) {
  return tfmap<modul<crane::obj, List<crane::obj>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> modul<crane::obj, List<crane::obj>> {
          return TFunctor_modul<List<crane::obj>>(
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
              _x0, crane_convert<modul<crane::obj, List<crane::obj>>>(_x1));
        };
      }(),
      [](const Nat &x) { return Nat::s(x); }, m);
}
