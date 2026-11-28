#include "case_handler_concrete_result.h"

std::shared_ptr<ITree<uint64_t>> CaseHandlerConcreteResult::tl() {
  return itree_trigger(sum1_inl(AE::A0));
}

std::shared_ptr<ITree<uint64_t>> CaseHandlerConcreteResult::tr() {
  return itree_trigger(sum1_inr(AE::A0));
}

uint64_t
CaseHandlerConcreteResult::result(uint64_t fuel,
                                  const std::shared_ptr<ITree<uint64_t>> &t) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    auto _cs = t->observe();
    if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
      uint64_t r = std::get_if<typename ITree<uint64_t>::Ret>(&_cs)->value;
      return r;
    } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
      std::shared_ptr<ITree<uint64_t>> t_ =
          std::get_if<typename ITree<uint64_t>::Tau>(&_cs)->next;
      return result(f, std::move(t_));
    } else {
      auto _x = crane_event_as<crane::obj>(
          std::get_if<typename ITree<uint64_t>::Vis>(&_cs)->effect);
      auto _x0 = std::get_if<typename ITree<uint64_t>::Vis>(&_cs)->cont;
      throw std::logic_error("absurd case");
    }
  }
}
