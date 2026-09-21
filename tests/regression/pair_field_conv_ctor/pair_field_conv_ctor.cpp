#include "pair_field_conv_ctor.h"

Ann<std::any> TFunctor_ann(std::function<std::any(std::any)> f,
                           const Ann<std::any> &a) {
  if (std::holds_alternative<typename Ann<std::any>::ANN_metadata>(a.v())) {
    const auto &[a0] = std::get<typename Ann<std::any>::ANN_metadata>(a.v());
    return Ann<std::any>::ann_metadata(a0.template map<std::any>(f));
  } else {
    const auto &[a0] = std::get<typename Ann<std::any>::ANN_prefix>(a.v());
    const auto &[t, e] = a0;
    return Ann<std::any>::ann_prefix(std::make_pair(
        std::any(crane_call_erased(f, t)),
        tfmap([](auto &&_ec0,
                 Exp0<std::any> _ec1) { return _ec1.TFunctor_exp(_ec0); },
              f, e)));
  }
}

Ann<Dt> run(const Ann<Nat> &a) {
  return tfmap<Ann>(
      [](auto &&_ec0, Ann<std::any> _ec1) { return TFunctor_ann(_ec0, _ec1); },
      [](Nat n) { return Dt::di(n); }, a);
}
