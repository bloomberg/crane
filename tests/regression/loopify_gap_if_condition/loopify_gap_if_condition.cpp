#include "loopify_gap_if_condition.h"

uint64_t LoopifyGapIfCondition::parity(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified parity: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t _tmp1 = std::move(_result);
      if (_tmp1 == UINT64_C(0)) {
        _result = UINT64_C(1);
      } else {
        _result = UINT64_C(0);
      }
    }
  }
  return _result;
}
