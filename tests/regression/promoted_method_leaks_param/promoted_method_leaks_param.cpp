#include "promoted_method_leaks_param.h"

std::shared_ptr<ITree<Nat>> PromotedMethodLeaksParam::use(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return raise0<FailE, Nat>(Nat::o());
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return itree_ret(a0);
  }
}
