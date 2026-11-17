#include "inlined_alias_resume_frame.h"

uint64_t InlinedAliasResumeFrame::h(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of h: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_h_in_S {
    uint64_t n;
    uint64_t m;
  };

  struct _after_h_in_S_2 {
    uint64_t n;
    uint64_t r1;
  };

  using _frame = std::variant<_call, _after_h_in_S, _after_h_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_h_in_S{n, m});
        _stack.emplace_back(_call{m});
      }
    } else if (std::holds_alternative<_after_h_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_h_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      uint64_t r1 = std::move(_result);
      _stack.emplace_back(_after_h_in_S_2{n, r1});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_h_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t r1 = _f.r1;
      uint64_t r2 = std::move(_result);
      _result = ((((r1 + r2) + n) + List<uint64_t>::nil().length()) +
                 List<bool>::nil().length());
    }
  }
  return _result;
}
