#include <loopify_itree_reified.h>

#include <any>
#include <crane_itree.h>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consumer fixpoint: traverses an ITree with fuel. This is a regular
/// fixpoint with recursion on fuel that processes reified ITrees. Should
/// be loopified normally (nontail with _Enter/_Call frames).
__attribute__((pure)) unsigned int
LoopifyItreeReified::count_taus(const unsigned int &fuel,
                                const std::shared_ptr<ITree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<ITree<unsigned int>> t;
    const unsigned int fuel;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const std::shared_ptr<ITree<unsigned int>> t = _f.t;
      const unsigned int fuel = _f.fuel;
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
          _stack.emplace_back(_Call1{});
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
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}
