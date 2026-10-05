#include "tfunctor_record_option_field.h"

TfunctorRecordOptionField::exp<crane::obj>
TfunctorRecordOptionField::TFunctor_exp(
    const crane::fn<crane::obj(crane::obj)> &f,
    const TfunctorRecordOptionField::exp<crane::obj> &e) {
  if (std::holds_alternative<
          typename TfunctorRecordOptionField::exp<crane::obj>::Lit>(e.v())) {
    const auto &[t0] =
        std::get<typename TfunctorRecordOptionField::exp<crane::obj>::Lit>(
            e.v());
    return exp<crane::obj>::lit(crane_call_erased(f, t0));
  } else {
    const auto &[e0] =
        std::get<typename TfunctorRecordOptionField::exp<crane::obj>::Neg>(
            e.v());
    return exp<crane::obj>::neg(TFunctor_exp(f, *e0));
  }
}

TfunctorRecordOptionField::global<crane::obj>
TfunctorRecordOptionField::TFunctor_global(
    const crane::fn<crane::obj(crane::obj)> &f,
    const TfunctorRecordOptionField::global<crane::obj> &g) {
  return global<crane::obj>{
      f(g.g_typ),
      tfmap<std::optional<TfunctorRecordOptionField::exp<crane::obj>>,
            crane::obj, crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0, const auto &_x1)
                       -> std::optional<
                           TfunctorRecordOptionField::exp<crane::obj>> {
              return TFunctor_option<
                  TfunctorRecordOptionField::exp<crane::obj>>(
                  TFunctor_exp, _x0,
                  crane_convert<std::optional<
                      TfunctorRecordOptionField::exp<crane::obj>>>(_x1));
            };
          }(),
          f, g.g_exp)};
}
