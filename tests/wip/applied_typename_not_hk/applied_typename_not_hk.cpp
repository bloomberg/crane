#include "applied_typename_not_hk.h"

std::shared_ptr<ITree<Nat>> AppliedTypenameNotHk::use(Nat n) {
  return h<AE, AE>(sum1_inl(AE::a0(std::move(n))));
}
