#include "loopify_gap_ackermann.h"

uint64_t
LoopifyGapAckermann::ack(uint64_t m,
                         uint64_t x0_) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t x0_;
    uint64_t m;
  };

  using _Frame = std::variant<_Enter>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{x0_, m});
  /// Loopified ack: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    uint64_t x0_ = _f.x0_;
    uint64_t m = _f.m;
    auto ack_n_impl = [&](auto &_self_ack_n, uint64_t n) -> uint64_t {
      if (m <= 0) {
        return (n + 1);
      } else {
        uint64_t m_ = m - 1;
        if (n <= 0) {
          return ack(m_, UINT64_C(1));
        } else {
          uint64_t n_ = n - 1;
          return ack(m_, _self_ack_n(_self_ack_n, n_));
        }
      }
    };
    auto ack_n = [&](uint64_t n) -> uint64_t {
      return ack_n_impl(ack_n_impl, n);
    };
    _result = ack_n(x0_);
  }
  return _result;
}
