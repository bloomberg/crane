#include "iter_callee_has_no_name.h"

std::shared_ptr<ITree<Nat>> IterCalleeHasNoName::countdown(const Nat &n) {
  return itree_iter(
      [](const Nat &k) {
        if (std::holds_alternative<typename Nat::O>(k.v())) {
          return itree_ret(Sum<Nat, Nat>::inr(Nat::o()));
        } else {
          const auto &[a0] = std::get<typename Nat::S>(k.v());
          return itree_ret(Sum<Nat, Nat>::inl(*a0));
        }
      },
      n);
}
