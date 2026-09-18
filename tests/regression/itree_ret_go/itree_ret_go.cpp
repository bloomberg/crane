#include "itree_ret_go.h"

std::shared_ptr<ITree<Nat>> ItreeRetGo::use(Nat n) {
  return itree_bind(itree_ret(std::move(n)),
                    [](Nat a) { return itree_ret(Nat::s(a)); });
}
