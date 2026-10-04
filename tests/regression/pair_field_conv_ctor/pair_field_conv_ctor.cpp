#include "pair_field_conv_ctor.h"

Ann<crane::obj> TFunctor_ann(crane::fn<crane::obj(crane::obj)> f,
                             const Ann<crane::obj> &a) {
  if (std::holds_alternative<typename Ann<crane::obj>::ANN_metadata>(a.v())) {
    const auto &[a0] = std::get<typename Ann<crane::obj>::ANN_metadata>(a.v());
    return Ann<crane::obj>::ann_metadata(
        a0.template map<crane::obj>(std::move(f)));
  } else {
    const auto &[a0] = std::get<typename Ann<crane::obj>::ANN_prefix>(a.v());
    const auto &[t, e] = a0;
    return Ann<crane::obj>::ann_prefix(
        std::make_pair(crane::obj(crane_call_erased(f, t)),
                       tfmap<Exp0<crane::obj>, crane::obj, crane::obj>(
                           [](auto &&_ec0, Exp0<crane::obj> _ec1) {
                             return _ec1.TFunctor_exp(_ec0);
                           },
                           f, e)));
  }
}

Ann<Dt> run(const Ann<Nat> &a) {
  return tfmap<Ann<crane::obj>, Nat, Dt>(
      [](auto &&_ec0, Ann<crane::obj> _ec1) {
        return TFunctor_ann(_ec0, _ec1);
      },
      [](const Nat &n) { return Dt::di(n); }, a);
}
