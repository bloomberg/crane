#include "hof_tree_loopify.h"

HofTreeLoopify::tree<uint64_t>
HofTreeLoopify::depth_tree(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0, n], resumes after recursive call with _result.
  struct _Resume_m {
    std::decay_t<decltype(tree<uint64_t>::leaf())> _s0;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  HofTreeLoopify::tree<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified depth_tree: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree<uint64_t>::leaf();
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{tree<uint64_t>::leaf(), n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = tree<uint64_t>::node(std::move(_result), _f.n, _f._s0);
    }
  }
  return _result;
}
