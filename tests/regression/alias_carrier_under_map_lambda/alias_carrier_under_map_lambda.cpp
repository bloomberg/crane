#include "alias_carrier_under_map_lambda.h"

texp<crane::obj>
TFunctor_texp(crane::fn<crane::obj(crane::obj)> f,
              const std::pair<crane::obj, Exp<crane::obj>> &p) {
  return std::make_pair(crane::obj(f(p.first)),
                        p.second.template exp_map<crane::obj>(f));
}

Instr<crane::obj> TFunctor_instr(crane::fn<crane::obj(crane::obj)> f,
                                 const Instr<crane::obj> &i) {
  if (std::holds_alternative<typename Instr<crane::obj>::I_op>(i.v())) {
    const auto &[a0] = std::get<typename Instr<crane::obj>::I_op>(i.v());
    return Instr<crane::obj>::i_op(
        tfmap<Exp<crane::obj>, crane::obj, crane::obj>(
            [](auto &&_ec0, Exp<crane::obj> _ec1) {
              return _ec1.TFunctor_exp(_ec0);
            },
            f, a0));
  } else {
    const auto &[a0, a1] = std::get<typename Instr<crane::obj>::I_call>(i.v());
    return Instr<crane::obj>::i_call(
        tfmap<texp<crane::obj>, crane::obj, crane::obj>(
            [](auto &&_ec0, texp<crane::obj> _ec1) {
              return TFunctor_texp(_ec0, _ec1);
            },
            f, a0),
        a1.template map<std::pair<texp<crane::obj>, Nat>>(
            [=](std::pair<texp<crane::obj>, Nat> pat) {
              const auto &[te, a] = pat;
              return std::make_pair(
                  tfmap<texp<crane::obj>, crane::obj, crane::obj>(
                      [](auto &&_ec0, texp<crane::obj> _ec1) {
                        return TFunctor_texp(_ec0, _ec1);
                      },
                      f, te),
                  a);
            }));
  }
}
