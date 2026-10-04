#include "coinductive_take_overflow.h"

CoinductiveTakeOverflow::stream<uint64_t> CoinductiveTakeOverflow::from(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter>;
  CoinductiveTakeOverflow::stream<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified from: CraneEnter.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<CraneEnter>(_frame));
    uint64_t n = _f.n;
    _result = stream<uint64_t>::lazy_(
        [=]() -> CoinductiveTakeOverflow::stream<uint64_t> {
          return stream<uint64_t>::cons(n, from((n + 1)));
        });
  }
  return _result;
}
