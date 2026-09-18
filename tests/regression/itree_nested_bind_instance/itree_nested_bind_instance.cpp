#include "itree_nested_bind_instance.h"

std::shared_ptr<ITree<Nat>> ItreeNestedBindInstance::use(Nat n) {
  return g<void>(itree_ret(std::move(n)));
}
