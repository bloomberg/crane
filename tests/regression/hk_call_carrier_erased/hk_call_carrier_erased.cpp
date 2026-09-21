#include "hk_call_carrier_erased.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = List<box<_CraneTcArg>>;
template <typename _CraneTcArg>
using _crane_carrier_tc1 = outer<_CraneTcArg, List<_CraneTcArg>>;

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b) {
  return box<std::any>{f(b.b_payload)};
}

Nat HkCallCarrierErased::bump(Nat n) { return Nat::s(std::move(n)); }

List<box<Nat>> HkCallCarrierErased::on_boxes(const List<box<Nat>> &l) {
  return tfmap<_crane_carrier_tc>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  List<std::any> _x1) -> List<std::any> {
          return TFunctor_list_<box>(
              [](auto &&_ec0, box<std::any> _ec1) {
                return TFunctor_box(_ec0, _ec1);
              },
              _x0, _x1);
        };
      }(),
      bump, l);
}

outer<Nat, List<Nat>>
HkCallCarrierErased::on_outer(const outer<Nat, List<Nat>> &m) {
  return tfmap<_crane_carrier_tc1>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  outer<std::any, std::any> _x1) -> outer<std::any, std::any> {
          return TFunctor_outer<List>(
              [](auto &&_ec0, List<std::any> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              _x0, _x1);
        };
      }(),
      bump, m);
}
