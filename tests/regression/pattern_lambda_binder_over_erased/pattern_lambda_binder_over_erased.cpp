#include "pattern_lambda_binder_over_erased.h"

List<crane::obj> TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(std::move(x0_));
}

Phi<crane::obj> TFunctor_phi(TFunctor<Exp0<crane::obj>> h,
                             crane::fn<crane::obj(crane::obj)> f,
                             const Phi<crane::obj> &p) {
  const auto &[es0] = p;
  return Phi<crane::obj>::phi0(
      tfmap<List<crane::obj>, std::pair<Nat, Exp0<crane::obj>>,
            std::pair<Nat, Exp0<crane::obj>>>(
          [](auto &&_ec0, List<crane::obj> _ec1) {
            return TFunctor_list(_ec0, _ec1);
          },
          [=](std::pair<Nat, Exp0<crane::obj>> ie) {
            const auto &[i, e] = ie;
            return std::make_pair(
                i, tfmap<Exp0<crane::obj>, crane::obj, crane::obj>(h, f, e));
          },
          es0));
}

Nat PatternLambdaBinderOverErased::bump(const Nat &n) { return Nat::s(n); }

Phi<Nat> PatternLambdaBinderOverErased::on_phi(const Phi<Nat> &p) {
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
