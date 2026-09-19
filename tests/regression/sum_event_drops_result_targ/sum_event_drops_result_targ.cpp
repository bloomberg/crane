#include "sum_event_drops_result_targ.h"

std::shared_ptr<ITree<std::pair<Nat, Nat>>>
SumEventDropsResultTarg::use(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return raise0<void, std::pair<Nat, Nat>>(Nat::o());
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return itree_ret(std::make_pair(a0, a0));
  }
}
