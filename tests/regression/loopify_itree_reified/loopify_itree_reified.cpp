#include "loopify_itree_reified.h"

/// Consumer fixpoint: traverses an ITree with fuel. This is a regular
/// fixpoint with recursion on fuel that processes reified ITrees. Should
/// be loopified normally (nontail with _Enter/_Call frames).
uint64_t
LoopifyItreeReified::count_taus(uint64_t fuel,
                                const std::shared_ptr<ITree<uint64_t>> &t) {
  // Explicit stack replaces the non-tail recursion of count_taus: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    std::shared_ptr<ITree<uint64_t>> t;
    uint64_t fuel;
  };

  struct _after_count_taus_in_TauF {};

  using _frame = std::variant<_call, _after_count_taus_in_TauF>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{t, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      std::shared_ptr<ITree<uint64_t>> t = std::move(_f.t);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        auto _cs = std::move(t)->observe();
        if (std::holds_alternative<typename ITree<uint64_t>::Ret>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<uint64_t>::Ret>(&_cs);
          auto _x = _itf.value;
          _result = UINT64_C(0);
        } else if (std::holds_alternative<typename ITree<uint64_t>::Tau>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<uint64_t>::Tau>(&_cs);
          auto t_ = _itf.next;
          _stack.emplace_back(_after_count_taus_in_TauF{});
          _stack.emplace_back(_call{std::move(t_), fuel_});
        } else {
          const auto &_itf = *std::get_if<typename ITree<uint64_t>::Vis>(&_cs);
          auto _x = crane_event_as<crane::obj>(_itf.effect);
          auto _x0 = _itf.cont;
          _result = UINT64_C(0);
        }
      }
    } else {
      auto _f = std::move(std::get<_after_count_taus_in_TauF>(_popped));
      _stack.pop_back();
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}
