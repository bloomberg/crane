#include "translate_applies_handler.h"

BE relabel(AE) { return BE::B1; }

std::shared_ptr<ITree<uint64_t>> TranslateAppliesHandler::t0() {
  return itree_trigger(AE::A0);
}

std::shared_ptr<ITree<uint64_t>> TranslateAppliesHandler::relabelled() {
  return itree_translate(
      [](const AE &a0) -> BE { return relabel(crane_convert<AE>(a0)); },
      t0());
}

std::shared_ptr<ITree<uint64_t>> TranslateAppliesHandler::injected() {
  return itree_translate([](AE e) { return sum1_inr(e); }, t0());
}

uint64_t TranslateAppliesHandler::which_b(BE e) {
  switch (e) {
  case BE::B0: {
    return UINT64_C(0);
  }
  case BE::B1: {
    return UINT64_C(1);
  }
  default:
    std::unreachable();
  }
}

uint64_t
TranslateAppliesHandler::which_side(const Sum1<AE, AE, crane::obj> &e) {
  if (std::holds_alternative<typename Sum1<AE, AE, crane::obj>::Inl1>(e.v())) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}

uint64_t
TranslateAppliesHandler::b_of(const std::shared_ptr<ITree<uint64_t>> &t) {
  auto _cs = t->observe();
  if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
    auto _x = _itf.value;
    return UINT64_C(9);
  } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
    auto _x = _itf.next;
    return UINT64_C(9);
  } else {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
    auto e = crane_event_as<BE>(_itf.effect);
    auto _x = _itf.cont;
    return which_b(e);
  }
}

uint64_t
TranslateAppliesHandler::side_of(const std::shared_ptr<ITree<uint64_t>> &t) {
  auto _cs = t->observe();
  if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
    auto _x = _itf.value;
    return UINT64_C(9);
  } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
    auto _x = _itf.next;
    return UINT64_C(9);
  } else {
    const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
    auto e = crane_event_as<Sum1<AE, AE, crane::obj>>(_itf.effect);
    auto _x = _itf.cont;
    return which_side(std::move(e));
  }
}
