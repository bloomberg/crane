#include "loopify_gap_ackermann.h"

uint64_t
LoopifyGapAckermann::ack(uint64_t m,
                         uint64_t x0_) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t x0_;
    uint64_t m;
  };

  /// _Enter_ack_n: captures varying parameters for each recursive call.
  struct _Enter_ack_n {
    uint64_t n;
    uint64_t m;
  };

  /// _Cont_n_: saves [m_], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t m_;
  };

  using _Frame = std::variant<_Enter, _Enter_ack_n, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{x0_, m});
  /// Loopified ack: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t x0_ = _f.x0_;
      uint64_t m = _f.m;
      _stack.emplace_back(_Enter_ack_n{x0_, m});
    } else if (std::holds_alternative<_Enter_ack_n>(_frame)) {
      auto _f = std::move(std::get<_Enter_ack_n>(_frame));
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      if (m <= 0) {
        _result = (n + 1);
      } else {
        uint64_t m_ = m - 1;
        if (n <= 0) {
          _stack.emplace_back(_Enter{UINT64_C(1), m_});
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(_Cont_n_{m_});
          _stack.emplace_back(_Enter_ack_n{n_, m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t m_ = _f.m_;
      _stack.emplace_back(_Enter{std::move(_result), m_});
    }
  }
  return _result;
}
