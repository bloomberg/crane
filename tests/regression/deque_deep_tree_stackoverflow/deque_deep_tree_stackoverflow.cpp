#include "deque_deep_tree_stackoverflow.h"

DequeDeepTreeStackoverflow::rose DequeDeepTreeStackoverflow::deep_tree(
    uint64_t depth) { /// CraneEnter: captures varying parameters for each
                      /// recursive call.

  struct CraneEnter {
    uint64_t depth;
  };

  /// CraneCont_n: resumes after recursive call, then processes rest.
  struct CraneCont_n {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_n>;
  DequeDeepTreeStackoverflow::rose _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{depth});
  /// Loopified deep_tree: CraneEnter -> CraneCont_n.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t depth = _f.depth;
      if (depth <= 0) {
        _result = rose::rleaf(UINT64_C(42));
      } else {
        uint64_t n = depth - 1;
        _stack.emplace_back(CraneCont_n{});
        _stack.emplace_back(CraneEnter{n});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n>(_frame));
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
