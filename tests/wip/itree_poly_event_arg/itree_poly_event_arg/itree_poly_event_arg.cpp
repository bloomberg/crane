#include "itree_poly_event_arg.h"

std::shared_ptr<ITree<Nat>> ItreePolyEventArg::use(Nat n) {
  return f<void>([=]() mutable -> std::shared_ptr<ITree<Nat>> {
    return ITree<Nat>::ret(
        std::shared_ptr<ITree<std::any>>::go((std::any(std::move(n)))));
  }());
}
