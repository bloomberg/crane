#include "applied_typename_not_hk.h"

std::shared_ptr<ITree<crane::obj>>
h(Sum1<crane::obj, Sum1<AE, crane::obj, crane::obj>, crane::obj> x) {
  return itree_case(
      E_trigger<crane::obj>,
      itree_case(
          [](const auto &_x) { return _x.template handle<crane::obj>(); },
          F_trigger<crane::obj>))(std::move(x));
}

std::shared_ptr<ITree<Nat>> AppliedTypenameNotHk::use(const Nat &n) {
  return crane_convert<std::shared_ptr<ITree<Nat>>>(h(sum1_inl(AE::a0(n))));
}
