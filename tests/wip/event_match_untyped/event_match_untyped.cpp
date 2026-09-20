#include "event_match_untyped.h"

/// The event is matched in the very branch that binds it, so nothing
/// downstream says what type it has.
Nat EventMatchUntyped::weight(const std::shared_ptr<ITree<Nat>> &t) {
  auto _cs = t->observe();
  if (std::holds_alternative<typename ITree<Nat>::Ret>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<Nat>::Ret>(&_cs);
    auto r = _itf.value;
    return r;
  } else if (std::holds_alternative<typename ITree<Nat>::Tau>(_cs)) {
    const auto &_itf = *std::get_if<typename ITree<Nat>::Tau>(&_cs);
    auto _x = _itf.next;
    return Nat::o();
  } else {
    const auto &_itf = *std::get_if<typename ITree<Nat>::Vis>(&_cs);
    crane_event e{_itf.effect};
    auto _x = _itf.cont;
    if (std::holds_alternative<typename EventMatchUntyped::IOE::Rd>(e.v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[a0] = std::get<typename EventMatchUntyped::IOE::Wr>(e.v());
      return a0;
    }
  }
}
