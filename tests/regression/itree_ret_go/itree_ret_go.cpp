#include "itree_ret_go.h"

std::shared_ptr<ITree<Nat>> ItreeRetGo::use(const Nat &n) {
  return itree_bind(itree_ret(n),
                    [](const Nat &a) { return itree_ret(Nat::s(a)); });
}
