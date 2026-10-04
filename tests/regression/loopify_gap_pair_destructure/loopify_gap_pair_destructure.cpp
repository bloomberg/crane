#include "loopify_gap_pair_destructure.h"

std::pair<uint64_t, uint64_t> LoopifyGapPairDestructure::swap_pair(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified swap_pair: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      auto [a, b] = std::move(_result);
      _result = std::make_pair(b, (a + 1));
    }
  }
  return _result;
}
