#include "sum_side_survives_vis.h"

std::shared_ptr<ITree<uint64_t>> SumSideSurvivesVis::tl() {
  return itree_trigger(sum1_inl(AE::A0));
}

std::shared_ptr<ITree<uint64_t>> SumSideSurvivesVis::tr() {
  return itree_trigger(sum1_inr(AE::A0));
}

std::shared_ptr<ITree<uint64_t>> SumSideSurvivesVis::vr() {
  return itree_vis(sum1_inr(AE::A0), [](const auto &n) {
    return itree_ret(crane::any_cast<uint64_t>(n));
  });
}

uint64_t
SumSideSurvivesVis::first_side(const std::shared_ptr<ITree<uint64_t>> &t) {
  auto _cs = t->observe();
  if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
    auto _x = _itf.value;
    return UINT64_C(0);
  } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
    auto _x = _itf.next;
    return UINT64_C(0);
  } else {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
    auto e = crane_event_as<Sum1<AE, AE, crane::obj>>(_itf.effect);
    auto _x = _itf.cont;
    return side<void>(e);
  }
}
