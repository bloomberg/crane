#include "loopify_gap_pair_destructure.h"

std::pair<uint64_t, uint64_t> LoopifyGapPairDestructure::swap_pair(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_m: resumes after recursive call, then processes rest.
  struct _Cont_m {};

  using _Frame = std::variant<_Enter, _Cont_m>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified swap_pair: _Enter -> _Cont_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Cont_m{});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Cont_m>(_frame));
      std::pair<uint64_t, uint64_t> _rc1 = std::move(_result);
      auto [a, b] = _rc1;
      _result = std::make_pair(b, (a + 1));
    }
  }
  return _result;
}
