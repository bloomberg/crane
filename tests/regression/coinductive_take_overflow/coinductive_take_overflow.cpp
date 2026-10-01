#include "coinductive_take_overflow.h"

CoinductiveTakeOverflow::stream<uint64_t> CoinductiveTakeOverflow::from(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter>;
  CoinductiveTakeOverflow::stream<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified from: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    uint64_t n = _f.n;
    _result = stream<uint64_t>::lazy_(
        [=]() -> CoinductiveTakeOverflow::stream<uint64_t> {
          return stream<uint64_t>::cons(n, from((n + 1)));
        });
  }
  return _result;
}
