#include "loopify_block_template_frame.h"

List<uint64_t> LoopifyBlockTemplateFrame::doubles(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [d], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t d;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified doubles: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        uint64_t d;
        d = n * 2;
        _stack.emplace_back(CraneCont_m{d});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t d = _f.d;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(d, std::move(rest));
    }
  }
  return _result;
}
