#include "loopify_gap_ackermann.h"

uint64_t
LoopifyGapAckermann::ack(uint64_t m,
                         uint64_t x0_) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t x0_;
    uint64_t m;
  };

  /// CraneEnter_ack_n: captures varying parameters for each recursive call.
  struct CraneEnter_ack_n {
    uint64_t n;
    uint64_t m;
  };

  /// CraneCont_n_: saves [m_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t m_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneEnter_ack_n, CraneCont_n_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{x0_, m});
  /// Loopified ack: CraneEnter -> CraneCont_n_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t x0_ = _f.x0_;
      uint64_t m = _f.m;
      _stack.emplace_back(CraneEnter_ack_n{x0_, m});
    } else if (std::holds_alternative<CraneEnter_ack_n>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_ack_n>(_frame));
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      if (m <= 0) {
        _result = (n + 1);
      } else {
        uint64_t m_ = m - 1;
        if (n <= 0) {
          _stack.emplace_back(CraneEnter{UINT64_C(1), m_});
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(CraneCont_n_{m_});
          _stack.emplace_back(CraneEnter_ack_n{n_, m});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t m_ = _f.m_;
      _stack.emplace_back(CraneEnter{std::move(_result), m_});
    }
  }
  return _result;
}
