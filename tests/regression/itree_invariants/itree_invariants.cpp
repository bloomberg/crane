#include "itree_invariants.h"

/// Emitted so the generated header includes <crane_itree.h>.
uint64_t
ItreeInvariants::count_taus(uint64_t fuel,
                            const std::shared_ptr<ITree<uint64_t>> &t) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t fuel_ = fuel - 1;
    auto _cs = t->observe();
    if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
      uint64_t _x = std::get_if<typename ITree<uint64_t>::Ret>(&_cs)->value;
      return UINT64_C(0);
    } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
      auto t_ = std::get_if<typename ITree<uint64_t>::Tau>(&_cs)->next;
      return (count_taus(fuel_, std::move(t_)) + 1);
    } else {
      auto _x = crane_event_as<crane::obj>(
          std::get_if<typename ITree<uint64_t>::Vis>(&_cs)->effect);
      auto _x0 = std::get_if<typename ITree<uint64_t>::Vis>(&_cs)->cont;
      return UINT64_C(0);
    }
  }
}
