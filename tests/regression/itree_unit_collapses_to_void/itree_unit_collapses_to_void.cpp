#include "itree_unit_collapses_to_void.h"

std::shared_ptr<ITree<Nat>> ItreeUnitCollapsesToVoid::get() {
  return itree_trigger(E::get());
}

std::shared_ptr<ITree<std::monostate>> ItreeUnitCollapsesToVoid::put(Nat n) {
  return itree_trigger(E::put(std::move(n)));
}

std::shared_ptr<ITree<std::monostate>> ItreeUnitCollapsesToVoid::both(bool b) {
  if (b) {
    return put(Nat::s(Nat::o()));
  } else {
    return itree_ret(std::monostate{});
  }
}

std::shared_ptr<ITree<std::monostate>> ItreeUnitCollapsesToVoid::prog() {
  return itree_bind(get(), [](const Nat &n) { return both(n.eqb(Nat::o())); });
}
