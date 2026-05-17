#include "loopify_itree_reified.h"

/// Consumer fixpoint: traverses an ITree with fuel. This is a regular
/// fixpoint with recursion on fuel that processes reified ITrees. Should
/// be loopified normally (nontail with _Enter/_Call frames).
unsigned int LoopifyItreeReified::count_taus(
    unsigned int fuel,
    const std::shared_ptr<ITree<unsigned int>>
        &t) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    std::shared_ptr<ITree<unsigned int>> t;
    unsigned int fuel;
  };

  /// _Resume_t_: resumes after recursive call with _result.
  struct _Resume_t_ {};

  using _Frame = std::variant<_Enter, _Resume_t_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{t, fuel});
  /// Loopified count_taus: _Enter -> _Resume_t_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const std::shared_ptr<ITree<unsigned int>> &t = _f.t;
      unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int fuel_ = fuel - 1;
        auto _cs = t->observe();
        if (std::holds_alternative<typename ITree<unsigned int>::Ret>(_cs)) {
          const auto &_itf =
              *std::get_if<typename ITree<unsigned int>::Ret>(&_cs);
          auto _x = _itf.value;
          _result = 0u;
        } else if (std::holds_alternative<typename ITree<unsigned int>::Tau>(
                       _cs)) {
          const auto &_itf =
              *std::get_if<typename ITree<unsigned int>::Tau>(&_cs);
          auto t_ = _itf.next;
          _stack.emplace_back(_Resume_t_{});
          _stack.emplace_back(_Enter{t_, fuel_});
        } else {
          const auto &_itf =
              *std::get_if<typename ITree<unsigned int>::Vis>(&_cs);
          auto _x = _itf.effect;
          auto _x0 = _itf.cont;
          _result = 0u;
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_t_>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}
