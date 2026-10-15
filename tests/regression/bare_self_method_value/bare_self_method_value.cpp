#include "bare_self_method_value.h"

List<Nat> BareSelfMethodValue::sizes(
    const List<BareSelfMethodValue::bareSelfMethodValue> &ts) {
  return ts.template map<Nat>(
      [](const BareSelfMethodValue::bareSelfMethodValue &_x) {
        return _x.size();
      });
}

Nat BareSelfMethodValue::total(
    const List<BareSelfMethodValue::bareSelfMethodValue> &ts) {
  return sizes(ts).template fold_left<Nat>(
      [](const Nat &_x0, const Nat &_x1) { return _x0.add(_x1); }, Nat::o());
}
