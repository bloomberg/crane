#include "loopify_gap_nested_fix.h"

uint64_t LoopifyGapNestedFix::rose_sum(
    const LoopifyGapNestedFix::rose
        &r) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyGapNestedFix::rose r;
  };

  using _Frame = std::variant<_Enter>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{r});
  /// Loopified rose_sum: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    const LoopifyGapNestedFix::rose &r = std::move(_f.r);
    const auto &[a0, a1] =
        std::get<typename LoopifyGapNestedFix::rose::Rose0>(r.v());
    auto sum_list_impl =
        [](auto &_self_sum_list,
           const List<LoopifyGapNestedFix::rose> &l) -> uint64_t {
      if (std::holds_alternative<typename List<LoopifyGapNestedFix::rose>::Nil>(
              l.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a2, a3] =
            std::get<typename List<LoopifyGapNestedFix::rose>::Cons>(l.v());
        return (rose_sum(a2) + _self_sum_list(_self_sum_list, *a3));
      }
    };
    auto sum_list = [&](const List<LoopifyGapNestedFix::rose> &l) -> uint64_t {
      return sum_list_impl(sum_list_impl, l);
    };
    _result = (a0 + sum_list(*a1));
  }
  return _result;
}

uint64_t LoopifyGapNestedFix::rose_sum_sample(std::monostate) {
  return rose_sum(sample_tree);
}
