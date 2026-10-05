#include "tfunctor_record_list_field.h"

List<crane::obj> TfunctorRecordListField::TFunctor_list(
    const crane::fn<crane::obj(crane::obj)> &x0_, const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(x0_);
}

TfunctorRecordListField::operand<crane::obj>
TfunctorRecordListField::TFunctor_operand(
    const crane::fn<crane::obj(crane::obj)> &f,
    const TfunctorRecordListField::operand<crane::obj> &o) {
  const auto &[t0] = o;
  return operand<crane::obj>::op(crane_call_erased(f, t0));
}

TfunctorRecordListField::bundle<crane::obj>
TfunctorRecordListField::TFunctor_bundle(
    const crane::fn<crane::obj(crane::obj)> &f,
    const TfunctorRecordListField::bundle<crane::obj> &b) {
  return bundle<crane::obj>{
      b.tag,
      tfmap<List<TfunctorRecordListField::operand<crane::obj>>, crane::obj,
            crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0, const auto &_x1)
                       -> List<TfunctorRecordListField::operand<crane::obj>> {
              return TFunctor_list_<
                  TfunctorRecordListField::operand<crane::obj>>(
                  [](auto &&_ec0,
                     TfunctorRecordListField::operand<crane::obj> _ec1) {
                    return TFunctor_operand(_ec0, _ec1);
                  },
                  _x0,
                  crane_convert<
                      List<TfunctorRecordListField::operand<crane::obj>>>(_x1));
            };
          }(),
          f, b.ops)};
}
