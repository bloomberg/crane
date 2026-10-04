#include "loopify_itree_reified.h"

/// Consumer fixpoint: traverses an ITree with fuel. This is a regular
/// fixpoint with recursion on fuel that processes reified ITrees. Should
/// be loopified normally (nontail with _Enter/_Call frames).
uint64_t
LoopifyItreeReified::count_taus(uint64_t fuel,
                                const std::shared_ptr<ITree<uint64_t>> &
                                    t) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    std::shared_ptr<ITree<uint64_t>> t;
    uint64_t fuel;
  };

  /// CraneCont_t_: resumes after recursive call, then processes rest.
  struct CraneCont_t_ {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_t_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{t, fuel});
  /// Loopified count_taus: CraneEnter -> CraneCont_t_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const std::shared_ptr<ITree<uint64_t>> &t = std::move(_f.t);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        auto _cs = t->observe();
        if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
          auto _x = _itf.value;
          _result = UINT64_C(0);
        } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
          auto t_ = _itf.next;
          _stack.emplace_back(CraneCont_t_{});
          _stack.emplace_back(CraneEnter{t_, fuel_});
        } else {
          const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
          auto _x = crane_event_as<crane::obj>(_itf.effect);
          auto _x0 = _itf.cont;
          _result = UINT64_C(0);
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_t_>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}
