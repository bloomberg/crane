#include "itree_poly_event_arg.h"

std::shared_ptr<ITree<Nat>> f(std::shared_ptr<ITree<Nat>> x) {
  return itree_bind(std::move(x),
                    [](const Nat &a) { return itree_ret(Nat::s(a)); });
}

std::shared_ptr<ITree<Nat>> ItreePolyEventArg::use(const Nat &n) {
  return f(itree_ret(n));
}
