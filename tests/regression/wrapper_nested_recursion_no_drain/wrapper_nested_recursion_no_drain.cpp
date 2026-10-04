#include "wrapper_nested_recursion_no_drain.h"

WrapperNestedRecursionNoDrain::rose WrapperNestedRecursionNoDrain::deep(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  WrapperNestedRecursionNoDrain::rose _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified deep: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = rose::rleaf(UINT64_C(42));
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
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
