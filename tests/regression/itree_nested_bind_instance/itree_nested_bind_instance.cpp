#include "itree_nested_bind_instance.h"

std::shared_ptr<ITree<Nat>> g(const std::shared_ptr<ITree<Nat>> &x) {
  return itree_bind(x, [=, x = x](const Nat &a) {
    return Monad_itree<crane::obj>::template bind<Nat, Nat>(
        x, [=, a = a](Nat b) {
          return Monad_itree<crane::obj>::template ret<Nat>(a.add(std::move(b)));
        });
  });
}

std::shared_ptr<ITree<Nat>> ItreeNestedBindInstance::use(const Nat &n) {
  return g(itree_ret(n));
}
