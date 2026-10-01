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
      const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
      auto r = _itf.value;
      return r;
    } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
      const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
      auto t_ = _itf.next;
      return result(f, t_);
    } else {
      const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
      auto _x = crane_event_as<crane::obj>(_itf.effect);
      auto _x0 = _itf.cont;
      throw std::logic_error("absurd case");
    }
  }
}
