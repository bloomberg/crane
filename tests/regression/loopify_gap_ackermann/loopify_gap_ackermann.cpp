#include "loopify_gap_ackermann.h"

uint64_t LoopifyGapAckermann::ack(uint64_t m, uint64_t x0_) {
  // Explicit stack replaces the non-tail recursion of ack: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t x0_;
    uint64_t m;
  };

  struct _call_ack_n {
    uint64_t n;
    uint64_t m;
  };

  struct _after_ack_n_in_S {
    uint64_t m_;
  };

  using _frame = std::variant<_call, _call_ack_n, _after_ack_n_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x0_, m});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t x0_ = _f.x0_;
      uint64_t m = _f.m;
      _stack.emplace_back(_call_ack_n{x0_, m});
    } else if (std::holds_alternative<_call_ack_n>(_popped)) {
      auto _f = std::move(std::get<_call_ack_n>(_popped));
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      if (m <= 0) {
        _result = (n + 1);
      } else {
        uint64_t m_ = m - 1;
        if (n <= 0) {
          _stack.emplace_back(_call{UINT64_C(1), m_});
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(_after_ack_n_in_S{m_});
          _stack.emplace_back(_call_ack_n{n_, m});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_ack_n_in_S>(_popped));
      uint64_t m_ = _f.m_;
      _stack.emplace_back(_call{std::move(_result), m_});
    }
  }
  return _result;
}
