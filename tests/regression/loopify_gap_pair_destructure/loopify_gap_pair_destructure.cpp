#include "loopify_gap_pair_destructure.h"

std::pair<uint64_t, uint64_t> LoopifyGapPairDestructure::swap_pair(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of swap_pair: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_swap_pair_in_S {};

  using _frame = std::variant<_call, _after_swap_pair_in_S>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_swap_pair_in_S{});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_swap_pair_in_S>(_popped));
      _stack.pop_back();
      auto [a, b] = std::move(_result);
      _result = std::make_pair(b, (a + 1));
    }
  }
  return _result;
}
