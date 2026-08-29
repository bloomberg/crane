#include "wrapper_nested_recursion_no_drain.h"

WrapperNestedRecursionNoDrain::rose WrapperNestedRecursionNoDrain::deep(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: resumes after recursive call with _result.
  struct _Resume_m {};

  using _Frame = std::variant<_Enter, _Resume_m>;
  WrapperNestedRecursionNoDrain::rose _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified deep: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = rose::rleaf(UINT64_C(42));
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = rose::rnode(
          box<WrapperNestedRecursionNoDrain::rose>::box0(std::move(_result)));
    }
  }
  return _result;
}

uint64_t WrapperNestedRecursionNoDrain::test_deep(uint64_t n) {
  auto &&_sv = deep(n);
  if (std::holds_alternative<
          typename WrapperNestedRecursionNoDrain::rose::RLeaf>(_sv.v())) {
    const auto &[a0] =
        std::get<typename WrapperNestedRecursionNoDrain::rose::RLeaf>(_sv.v());
    return a0;
  } else {
    return UINT64_C(0);
  }
}
