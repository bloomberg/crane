#ifndef INCLUDED_LOOPIFY_ITREE_REIFIED
#define INCLUDED_LOOPIFY_ITREE_REIFIED

#include "small_vector.h"
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct LoopifyItreeReified {
  static uint64_t count_taus(uint64_t fuel,
                             const std::shared_ptr<ITree<uint64_t>> &t);

  template <typename T1, typename F0>
  static std::shared_ptr<ITree<T1>> pass_body(F0 &&rec,
                                              const itreeF_t<T1> &ot) {
    if (std::holds_alternative<typename ITree<T1>::Ret>(ot)) {
      const auto &_itf = *std::get_if<typename ITree<T1>::Ret>(&ot);
      auto r = _itf.value;
      return ITree<T1>::ret(r);
    } else if (std::holds_alternative<typename ITree<T1>::Tau>(ot)) {
      const auto &_itf = *std::get_if<typename ITree<T1>::Tau>(&ot);
      auto t_ = _itf.next;
      return [&]() {
        auto t = rec(t_);
        return ITree<decltype(t->run())>::tau(t);
      }();
    } else {
      const auto &_itf = *std::get_if<typename ITree<T1>::Vis>(&ot);
      auto e = _itf.effect;
      auto k = _itf.cont;
      return itree_vis(e, [=](const auto &x) mutable { return rec(k(x)); });
    }
  }

  template <typename T1>
  static std::shared_ptr<ITree<T1>> pass(const std::shared_ptr<ITree<T1>> &t) {
    return pass_body<T1>(pass<T1>, t->observe());
  }

  static inline const uint64_t test_count =
      count_taus(UINT64_C(100), ITree<uint64_t>::ret(UINT64_C(42)));
};

#endif // INCLUDED_LOOPIFY_ITREE_REIFIED
