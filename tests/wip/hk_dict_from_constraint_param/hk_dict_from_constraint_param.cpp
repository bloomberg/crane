#include "hk_dict_from_constraint_param.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = holder<_CraneTcArg, List<_CraneTcArg>>;

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_) {
  return x1_.template map<std::any>(std::move(x0_));
}

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b) {
  return box<std::any>{f(b.b_payload)};
}

holder<Nat, List<Nat>>
HkDictFromConstraintParam::run(const holder<Nat, List<Nat>> &m) {
  return tfmap<_crane_carrier_tc>(
      []() {
        return
            [](std::function<std::any(std::any)> _x0,
               holder<std::any, std::any> _x1) -> holder<std::any, std::any> {
              return TFunctor_holder<List>(
                  [](auto &&_ec0, List<std::any> _ec1) {
                    return TFunctor_list(_ec0, _ec1);
                  },
                  [](auto &&_ec0, box<std::any> _ec1) {
                    return TFunctor_box(_ec0, _ec1);
                  },
                  _x0, _x1);
            };
      }(),
      [](Nat x) { return Nat::s(x); }, m);
}
