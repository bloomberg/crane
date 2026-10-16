#include "promoted_module_static_fn_undefined.h"

List<Nat> PromotedModuleStaticFnUndefined::sizes(
    const List<PromotedModuleStaticFnUndefined> &ts) {
  return ts.template map<Nat>([](const PromotedModuleStaticFnUndefined &t) {
    return Nat::s(t.size());
  });
}

Nat PromotedModuleStaticFnUndefined::total(
    const List<PromotedModuleStaticFnUndefined> &ts) {
  return sizes(ts).template fold_left<Nat>(
      [](const Nat &_x0, const Nat &_x1) { return _x0.add(_x1); }, Nat::o());
}

Nat PromotedModuleStaticFnUndefined::example(const Nat &n) {
  return total(List<PromotedModuleStaticFnUndefined>::cons(
      PromotedModuleStaticFnUndefined::leaf(),
      List<PromotedModuleStaticFnUndefined>::cons(
          PromotedModuleStaticFnUndefined::node(
              PromotedModuleStaticFnUndefined::leaf(), n,
              PromotedModuleStaticFnUndefined::leaf()),
          List<PromotedModuleStaticFnUndefined>::nil())));
}
