#include "hk_dict_from_constraint_param.h"

List<crane::obj> TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(std::move(x0_));
}

box<crane::obj> TFunctor_box(crane::fn<crane::obj(crane::obj)> f,
                             const box<crane::obj> &b) {
  return box<crane::obj>{f(b.b_payload)};
}

holder<Nat, List<Nat>>
HkDictFromConstraintParam::run(const holder<Nat, List<Nat>> &m) {
  return tfmap<holder<crane::obj, List<crane::obj>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> holder<crane::obj, List<crane::obj>> {
          return TFunctor_holder<List<crane::obj>>(
              [](auto &&_ec0, List<crane::obj> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              [](auto &&_ec0, box<crane::obj> _ec1) {
                return TFunctor_box(_ec0, _ec1);
              },
              _x0, crane_convert<holder<crane::obj, List<crane::obj>>>(_x1));
        };
      }(),
      [](const Nat &x) { return Nat::s(x); }, m);
}
