#include "handler_case_has_no_name.h"

std::shared_ptr<ITree<crane::obj>> e_trigger(AE e) { return itree_trigger(e); }

std::shared_ptr<ITree<crane::obj>> b_trigger(BE e) { return itree_trigger(e); }

std::shared_ptr<ITree<crane::obj>> h(Sum1<AE, BE, crane::obj> x) {
  return itree_case(e_trigger, b_trigger)(std::move(x));
}

std::shared_ptr<ITree<Nat>> HandlerCaseHasNoName::use(const Nat &n) {
  return Interp::template interp<Monad_itree<Eff<crane::obj>>,
                                 Functor_itree<Eff<crane::obj>>,
                                 Sum1<AE, BE, crane::obj>, Nat>(
      MonadIter_itree<void>, h, itree_ret(n));
}
