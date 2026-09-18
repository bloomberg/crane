#include "itree_ret_go.h"

std::shared_ptr<ITree<Nat>> ItreeRetGo::use(Nat n) {
  return itree_bind(
      [=]() mutable -> std::shared_ptr<ITree<Nat>> {
        return ITree<Nat>::ret(
            std::shared_ptr<ITree<std::any>>::go((std::any(std::move(n)))));
      }(),
      [](Nat a) {
        return std::shared_ptr<ITree<std::any>>::go((std::any(Nat::s(a))));
      });
}
