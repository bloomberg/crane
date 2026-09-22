#include "hk_instance_body_targ_undeclared.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = std::optional<List<_CraneTcArg>>;
template <typename _CraneTcArg>
using _crane_carrier_tc1 = List<List<_CraneTcArg>>;

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

Nat HkInstanceBodyTargUndeclared::bump(Nat n) { return Nat::s(std::move(n)); }

std::optional<List<Nat>>
HkInstanceBodyTargUndeclared::on_option(const std::optional<List<Nat>> &o) {
  return tfmap<_crane_carrier_tc>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  std::optional<List<std::any>> _x1)
                   -> std::optional<List<std::any>> {
          return TFunctor_option<List>(
              [](auto &&_ec0, List<std::any> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              _x0, _x1);
        };
      }(),
      bump, o);
}

List<List<Nat>>
HkInstanceBodyTargUndeclared::on_list(const List<List<Nat>> &l) {
  return tfmap<_crane_carrier_tc1>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  List<List<std::any>> _x1) -> List<List<std::any>> {
          return TFunctor_list_<List>(
              [](auto &&_ec0, List<std::any> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              _x0, _x1);
        };
      }(),
      bump, l);
}
