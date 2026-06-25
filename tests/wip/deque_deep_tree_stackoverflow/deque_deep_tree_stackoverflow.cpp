#include "deque_deep_tree_stackoverflow.h"

DequeDeepTreeStackoverflow::rose DequeDeepTreeStackoverflow::deep_tree(
    uint64_t depth) { /// _Enter: captures varying parameters for each recursive
                      /// call.

  struct _Enter {
    uint64_t depth;
  };

  /// _Resume_n: saves [_s0], resumes after recursive call with _result.
  struct _Resume_n {
    std::decay_t<decltype(std::deque<DequeDeepTreeStackoverflow::rose>{})> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_n>;
  DequeDeepTreeStackoverflow::rose _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{depth});
  /// Loopified deep_tree: _Enter -> _Resume_n.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t depth = _f.depth;
      if (depth <= 0) {
        _result = rose::rleaf(UINT64_C(42));
      } else {
        uint64_t n = depth - 1;
        _stack.emplace_back(
            _Resume_n{std::deque<DequeDeepTreeStackoverflow::rose>{}});
        _stack.emplace_back(_Enter{n});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n>(_frame));
      _result = rose::rnode([](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(std::move(_result), _f._s0));
    }
  }
  return _result;
}

uint64_t DequeDeepTreeStackoverflow::test_deep(uint64_t n) {
  auto &&_sv = deep_tree(n);
  if (std::holds_alternative<typename DequeDeepTreeStackoverflow::rose::RLeaf>(
          _sv.v())) {
    const auto &[a0] =
        std::get<typename DequeDeepTreeStackoverflow::rose::RLeaf>(_sv.v());
    return a0;
  } else {
    return UINT64_C(0);
  }
}
