#include "loopify_gap_if_condition.h"

uint64_t LoopifyGapIfCondition::parity(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of parity: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_parity_in_S {};

  using _frame = std::variant<_call, _after_parity_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_parity_in_S{});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_parity_in_S>(_popped));
      if (std::move(_result) == UINT64_C(0)) {
        _result = UINT64_C(1);
      } else {
        _result = UINT64_C(0);
      }
    }
  }
  return _result;
}
