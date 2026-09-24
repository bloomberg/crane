#include "pattern_lambda_binder_over_erased.h"

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

Phi<std::any> TFunctor_phi(std::type_identity_t<TFunctor<Exp0>> h,
                           std::function<std::any(std::any)> f,
                           const Phi<std::any> &p) {
  const auto &[es0] = p;
  return Phi<std::any>::phi0(
      tfmap<List>([](auto &&_ec0,
                     List<std::any> _ec1) { return TFunctor_list(_ec0, _ec1); },
                  [=](std::pair<Nat, Exp0<std::any>> ie) mutable {
                    const auto &[i, e] = ie;
                    return std::make_pair(
                        std::any_cast<Nat>(i),
                        tfmap<Exp0>(h, f, std::any_cast<Exp0<std::any>>(e)));
                  },
                  es0));
}

Nat PatternLambdaBinderOverErased::bump(Nat n) { return Nat::s(std::move(n)); }

Phi<Nat> PatternLambdaBinderOverErased::on_phi(const Phi<Nat> &p) {
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
