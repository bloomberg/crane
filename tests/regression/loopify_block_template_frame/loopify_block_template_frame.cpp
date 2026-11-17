#include "loopify_block_template_frame.h"

List<uint64_t> LoopifyBlockTemplateFrame::doubles(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of doubles: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_doubles_in_S {
    uint64_t d;
  };

  using _frame = std::variant<_call, _after_doubles_in_S>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t m = n - 1;
        uint64_t d;
        d = n * 2;
        _stack.emplace_back(_after_doubles_in_S{d});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_doubles_in_S>(_popped));
      uint64_t d = _f.d;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(d, std::move(rest));
    }
  }
  return _result;
}
