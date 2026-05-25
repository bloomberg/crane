#include "mem_safety_probe3.h"

/// TEST 10: Large tree with deep recursion — stresses the
/// loopified tree traversal and clone mechanisms.
MemSafetyProbe3::tree MemSafetyProbe3::build_deep(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [_s0, n], resumes after recursive call with _result.
  struct _Resume_n_ {
    std::decay_t<decltype(tree::leaf())> _s0;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  MemSafetyProbe3::tree _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified build_deep: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{tree::leaf(), n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = tree::node(_result, _f.n, _f._s0);
    }
  }
  return _result;
}
