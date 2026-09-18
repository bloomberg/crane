#include "itree_poly_event_arg.h"

std::shared_ptr<ITree<Nat>> ItreePolyEventArg::use(Nat n) {
  return f<void>(itree_ret(std::move(n)));
}
