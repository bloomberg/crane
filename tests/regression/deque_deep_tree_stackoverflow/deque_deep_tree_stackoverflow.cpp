#include "deque_deep_tree_stackoverflow.h"

DequeDeepTreeStackoverflow::rose DequeDeepTreeStackoverflow::deep_tree(
    uint64_t depth) { /// _Enter: captures varying parameters for each recursive
                      /// call.

  struct _Enter {
    uint64_t depth;
  };

  /// _Cont_n: resumes after recursive call, then processes rest.
  struct _Cont_n {};

  using _Frame = std::variant<_Enter, _Cont_n>;
  DequeDeepTreeStackoverflow::rose _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{depth});
  /// Loopified deep_tree: _Enter -> _Cont_n.
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
        _stack.emplace_back(_Cont_n{});
        _stack.emplace_back(_Enter{n});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n>(_frame));
      _result = rose::rnode([](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(std::move(_result), std::deque<DequeDeepTreeStackoverflow::rose>{}));
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
