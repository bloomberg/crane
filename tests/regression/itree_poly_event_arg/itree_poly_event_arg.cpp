#include "itree_poly_event_arg.h"

std::shared_ptr<ITree<Nat>> f(const std::shared_ptr<ITree<Nat>> &x) {
  return itree_bind(x, [](const Nat &a) { return itree_ret(Nat::s(a)); });
}

std::shared_ptr<ITree<Nat>> ItreePolyEventArg::use(const Nat &n) {
  return f(itree_ret(n));
}
