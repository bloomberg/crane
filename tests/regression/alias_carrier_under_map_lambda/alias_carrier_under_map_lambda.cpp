#include "alias_carrier_under_map_lambda.h"

texp<std::any> TFunctor_texp(std::function<std::any(std::any)> f,
                             const std::pair<std::any, Exp<std::any>> &p) {
  return std::make_pair(std::any(f(p.first)),
                        p.second.template exp_map<std::any>(f));
}

Instr<std::any> TFunctor_instr(std::function<std::any(std::any)> f,
                               const Instr<std::any> &i) {
  if (std::holds_alternative<typename Instr<std::any>::I_op>(i.v())) {
    const auto &[a0] = std::get<typename Instr<std::any>::I_op>(i.v());
    return Instr<std::any>::i_op(tfmap<Exp>(
        [](auto &&_ec0, Exp<std::any> _ec1) { return _ec1.TFunctor_exp(_ec0); },
        f, a0));
  } else {
    const auto &[a0, a1] = std::get<typename Instr<std::any>::I_call>(i.v());
    return Instr<std::any>::i_call(
        tfmap<texp>(
            [](auto &&_ec0, texp<std::any> _ec1) {
              return TFunctor_texp(_ec0, _ec1);
            },
            f, a0),
        a1.template map<std::any>(
            [=](std::pair<texp<std::any>, Nat> pat) mutable {
              const auto &[te, a] = pat;
              return std::make_pair(tfmap<texp>(
                                        [](auto &&_ec0, texp<std::any> _ec1) {
                                          return TFunctor_texp(_ec0, _ec1);
                                        },
                                        f, te),
                                    a);
            }));
  }
}
