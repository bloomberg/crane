#include "hk_carrier_alias_applied_as_type.h"

template <typename _CraneTcArg>
using _crane_carrier_tc_ca986222598eb83d =
    modul<_CraneTcArg, List<_CraneTcArg>>;

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

modul<Nat, List<Nat>>
HkCarrierAliasAppliedAsType::run(const modul<Nat, List<Nat>> &m) {
  return tfmap<_crane_carrier_tc_ca986222598eb83d>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  modul<std::any, List<std::any>> _x1)
                   -> modul<std::any, List<std::any>> {
          return TFunctor_modul<List>(
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
