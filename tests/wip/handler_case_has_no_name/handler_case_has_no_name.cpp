#include "handler_case_has_no_name.h"

std::shared_ptr<ITree<std::any>> e_trigger(AE e) { return itree_trigger(e); }

std::shared_ptr<ITree<std::any>> b_trigger(BE e) { return itree_trigger(e); }

std::shared_ptr<ITree<std::any>> h(Sum1<AE, BE, std::any> x) {
  return itree_case(e_trigger, b_trigger)(std::move(x));
}

std::shared_ptr<ITree<Nat>> HandlerCaseHasNoName::use(Nat n) {
  return Interp::template interp<Monad_itree<std::any>>(
      [](std::function<std::shared_ptr<ITree<Sum<std::any, std::any>>>(
             std::any)>
             _x0) -> std::shared_ptr<ITree<std::any>> { return <void>()(_x0); },
      h, itree_ret(std::move(n)));
}
