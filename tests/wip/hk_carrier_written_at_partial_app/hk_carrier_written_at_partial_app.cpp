#include "hk_carrier_written_at_partial_app.h"

Phi<crane::obj> TFunctor_phi(TFunctor<Exp0<crane::obj>> h,
                             crane::fn<crane::obj(crane::obj)> f,
                             const Phi<crane::obj> &p) {
  const auto &[es0] = p;
  return Phi<crane::obj>::phi0(es0.template map<Exp0<crane::obj>>(
      [=]<typename T1>(Exp0<T1> _x0) -> Exp0<crane::obj> {
        return tfmap<Exp0<crane::obj>, crane::obj, crane::obj>(h, f, _x0);
      }));
}

Nat HkCarrierWrittenAtPartialApp::bump(const Nat &n) { return Nat::s(n); }

Phi<Nat> HkCarrierWrittenAtPartialApp::on_phi(const Phi<Nat> &p) {
  return tfmap<Phi<crane::obj>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> Phi<crane::obj> {
          return TFunctor_phi(
              [](auto &&_ec0, Exp0<crane::obj> _ec1) {
                return _ec1.TFunctor_exp(_ec0);
              },
              _x0, crane_convert<Phi<crane::obj>>(_x1));
        };
      }(),
      bump, p);
}
