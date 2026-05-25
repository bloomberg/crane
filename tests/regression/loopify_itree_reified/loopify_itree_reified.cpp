#include "loopify_itree_reified.h"

/// Consumer fixpoint: traverses an ITree with fuel. This is a regular
/// fixpoint with recursion on fuel that processes reified ITrees. Should
/// be loopified normally (nontail with _Enter/_Call frames).
uint64_t
LoopifyItreeReified::count_taus(uint64_t fuel,
                                const std::shared_ptr<ITree<uint64_t>> &t) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t fuel_ = fuel - 1;
    auto _cs = t->observe();
    if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
      const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
      auto _x = _itf.value;
      return UINT64_C(0);
    } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
      const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
      auto t_ = _itf.next;
      return (count_taus(fuel_, t_) + 1);
    } else {
      const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
      auto _x = _itf.effect;
      auto _x0 = _itf.cont;
      return UINT64_C(0);
    }
  }
}
