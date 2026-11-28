#include "event_match_untyped.h"

/// The event is matched in the very branch that binds it, so nothing
/// downstream says what type it has.
Nat EventMatchUntyped::weight(const std::shared_ptr<ITree<Nat>> &t) {
  auto _cs = t->observe();
  if (std::holds_alternative<typename ITree<Nat>::Ret>(_cs)) {
    Nat r = std::get_if<typename ITree<Nat>::Ret>(&_cs)->value;
    return r;
  } else if (std::holds_alternative<typename ITree<Nat>::Tau>(_cs)) {
    std::shared_ptr<ITree<Nat>> _x =
        std::get_if<typename ITree<Nat>::Tau>(&_cs)->next;
    return Nat::o();
  } else {
    auto e = crane_event_as<EventMatchUntyped::IOE>(
        std::get_if<typename ITree<Nat>::Vis>(&_cs)->effect);
    auto _x = std::get_if<typename ITree<Nat>::Vis>(&_cs)->cont;
    if (std::holds_alternative<typename EventMatchUntyped::IOE::Rd>(e.v_mut())) {
      return Nat::s(Nat::o());
    } else {
      auto &[a0] = std::get<typename EventMatchUntyped::IOE::Wr>(e.v_mut());
      return std::move(a0);
    }
  }
}
