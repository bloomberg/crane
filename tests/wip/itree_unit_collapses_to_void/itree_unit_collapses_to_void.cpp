#include "itree_unit_collapses_to_void.h"

std::shared_ptr<ITree<Nat>> ItreeUnitCollapsesToVoid::get() {
  return itree_trigger(E::get());
}

void ItreeUnitCollapsesToVoid::put(Nat n) {
  {
    itree_trigger(E::put(std::move(n)));
    return;
  }
}

void ItreeUnitCollapsesToVoid::both(bool b) {
  if (b) {
    put(Nat::s(Nat::o()));
    return;
  } else {
    {
      itree_ret(std::monostate{});
      return;
    }
  }
}

std::shared_ptr<ITree<void>> ItreeUnitCollapsesToVoid::prog() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<Nat>> { return ITree<Nat>::ret(get()); }(),
      [](const Nat &n) {
        both(n.eqb(Nat::o()));
        return std::monostate{};
      });
}
