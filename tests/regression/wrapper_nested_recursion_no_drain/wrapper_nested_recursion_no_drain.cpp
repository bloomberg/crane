#include "wrapper_nested_recursion_no_drain.h"

WrapperNestedRecursionNoDrain::rose
WrapperNestedRecursionNoDrain::deep(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of deep: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_deep_in_S {};

  using _frame = std::variant<_call, _after_deep_in_S>;
  WrapperNestedRecursionNoDrain::rose _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = rose::rleaf(UINT64_C(42));
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_deep_in_S{});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_deep_in_S>(_popped));
      _stack.pop_back();
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
