#include "hk_carrier_written_at_partial_app.h"

template <typename _CraneTcArg>
using _crane_carrier_tc_67a3b72bb694a043 =
    std::function<Exp0<_CraneTcArg>(Exp0<std::any>)>;

Phi<std::any> TFunctor_phi(std::type_identity_t<TFunctor<Exp0>> h,
                           std::function<std::any(std::any)> f,
                           const Phi<std::any> &p) {
  const auto &[es0] = p;
  return Phi<std::any>::phi0(es0.template map<std::any>(
      tfmap<_crane_carrier_tc_67a3b72bb694a043>(std::move(h), std::move(f))));
}

Nat HkCarrierWrittenAtPartialApp::bump(Nat n) { return Nat::s(std::move(n)); }

Phi<Nat> HkCarrierWrittenAtPartialApp::on_phi(const Phi<Nat> &p) {
  return tfmap<Phi>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  Phi<std::any> _x1) -> Phi<std::any> {
          return TFunctor_phi(
              [](auto &&_ec0, Exp0<std::any> _ec1) {
                return _ec1.TFunctor_exp(_ec0);
              },
              _x0, _x1);
        };
      }(),
      bump, p);
}
