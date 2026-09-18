#include "itree_nested_bind_instance.h"

std::shared_ptr<ITree<Nat>> ItreeNestedBindInstance::use(Nat n) {
  return g<void>([=]() mutable -> std::shared_ptr<ITree<Nat>> {
    return ITree<Nat>::ret(
        std::shared_ptr<ITree<std::any>>::go((std::any(std::move(n)))));
  }());
}
