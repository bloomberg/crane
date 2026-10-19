#include "inlined_alias_resume_frame.h"

uint64_t
InlinedAliasResumeFrame::h(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [m, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m {
    uint64_t m;
    uint64_t n;
  };

  /// CraneCont_m_1: saves [n, r1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_m_1 {
    uint64_t n;
    uint64_t r1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m, CraneCont_m_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified h: CraneEnter -> CraneCont_m -> CraneCont_m_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{m, n});
        _stack.emplace_back(CraneEnter{m});
      }
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t m = _f.m;
      uint64_t n = _f.n;
      uint64_t r1 = std::move(_result);
      _stack.emplace_back(CraneCont_m_1{n, r1});
      _stack.emplace_back(CraneEnter{m});
    } else {
      auto _f = std::move(std::get<CraneCont_m_1>(_frame));
      uint64_t n = _f.n;
      uint64_t r1 = _f.r1;
      uint64_t r2 = std::move(_result);
      _result = ((((r1 + r2) + n) + List<uint64_t>::nil().length()) +
                 List<bool>::nil().length());
    }
  }
  return _result;
}
