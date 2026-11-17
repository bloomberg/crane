#include "deque_deep_tree_stackoverflow.h"

DequeDeepTreeStackoverflow::rose
DequeDeepTreeStackoverflow::deep_tree(uint64_t depth) {
  // Explicit stack replaces the non-tail recursion of deep_tree: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t depth;
  };

  struct _after_deep_tree_in_S {};

  using _frame = std::variant<_call, _after_deep_tree_in_S>;
  DequeDeepTreeStackoverflow::rose _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{depth});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t depth = _f.depth;
      if (depth <= 0) {
        _result = rose::rleaf(UINT64_C(42));
      } else {
        uint64_t n = depth - 1;
        _stack.emplace_back(_after_deep_tree_in_S{});
        _stack.emplace_back(_call{n});
      }
    } else {
      auto _f = std::move(std::get<_after_deep_tree_in_S>(_popped));
      _stack.pop_back();
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
