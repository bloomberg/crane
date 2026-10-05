#include "tfunctor_alias_carrier.h"

TfunctorAliasCarrier::exp<crane::obj> TfunctorAliasCarrier::TFunctor_exp(
    const crane::fn<crane::obj(crane::obj)> &f,
    const TfunctorAliasCarrier::exp<crane::obj> &e) {
  if (std::holds_alternative<
          typename TfunctorAliasCarrier::exp<crane::obj>::Lit>(e.v())) {
    const auto &[t0] =
        std::get<typename TfunctorAliasCarrier::exp<crane::obj>::Lit>(e.v());
    return exp<crane::obj>::lit(crane_call_erased(f, t0));
  } else {
    const auto &[e0] =
        std::get<typename TfunctorAliasCarrier::exp<crane::obj>::Neg>(e.v());
    return exp<crane::obj>::neg(TFunctor_exp(f, *e0));
  }
}

TfunctorAliasCarrier::texp<crane::obj> TfunctorAliasCarrier::TFunctor_texp(
    TfunctorAliasCarrier::TFunctor<TfunctorAliasCarrier::exp<crane::obj>> h,
    const crane::fn<crane::obj(crane::obj)> &f,
    const std::pair<crane::obj, TfunctorAliasCarrier::exp<crane::obj>> &pat) {
  const auto &[t, e] = pat;
  return std::make_pair(
      crane::obj(crane_call_erased(f, t)),
      tfmap<TfunctorAliasCarrier::exp<crane::obj>, crane::obj, crane::obj>(
          std::move(h), f, e));
}

TfunctorAliasCarrier::cmpxchg<crane::obj>
TfunctorAliasCarrier::TFunctor_cmpxchg(
    const crane::fn<crane::obj(crane::obj)> &f,
    const TfunctorAliasCarrier::cmpxchg<crane::obj> &c) {
  return cmpxchg<crane::obj>{
      tfmap<TfunctorAliasCarrier::texp<crane::obj>, crane::obj, crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0, const auto &_x1)
                       -> TfunctorAliasCarrier::texp<crane::obj> {
              return TFunctor_texp(
                  TFunctor_exp, _x0,
                  crane_convert<TfunctorAliasCarrier::texp<crane::obj>>(_x1));
            };
          }(),
          f, c.c_ptr),
      tfmap<TfunctorAliasCarrier::texp<crane::obj>, crane::obj, crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0, const auto &_x1)
                       -> TfunctorAliasCarrier::texp<crane::obj> {
              return TFunctor_texp(
                  TFunctor_exp, _x0,
                  crane_convert<TfunctorAliasCarrier::texp<crane::obj>>(_x1));
            };
          }(),
          f, c.c_new)};
}
