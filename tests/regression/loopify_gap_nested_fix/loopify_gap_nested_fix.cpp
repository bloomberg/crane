#include "loopify_gap_nested_fix.h"

uint64_t LoopifyGapNestedFix::rose_sum(const LoopifyGapNestedFix::rose &r) {
  // Explicit stack replaces the non-tail recursion of rose_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyGapNestedFix::rose *r;
  };

  struct _call_sum_list {
    const List<LoopifyGapNestedFix::rose> *l;
  };

  struct _after_rose_sum_in_Cons {
    const List<LoopifyGapNestedFix::rose> *a10;
  };

  struct _after_sum_list_in_Cons {
    uint64_t _tmp2;
  };

  struct _after_sum_list_in_Rose0 {
    uint64_t a0;
  };

  using _frame =
      std::variant<_call, _call_sum_list, _after_rose_sum_in_Cons,
                   _after_sum_list_in_Cons, _after_sum_list_in_Rose0>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&r});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyGapNestedFix::rose &r = *_f.r;
      const auto &[a0, a1] =
          std::get<typename LoopifyGapNestedFix::rose::Rose0>(r.v());
      _stack.emplace_back(_after_sum_list_in_Rose0{a0});
      _stack.emplace_back(_call_sum_list{crane_raw(a1)});
    } else if (std::holds_alternative<_call_sum_list>(_popped)) {
      auto _f = std::move(std::get<_call_sum_list>(_popped));
      _stack.pop_back();
      const List<LoopifyGapNestedFix::rose> &l = *_f.l;
      if (std::holds_alternative<typename List<LoopifyGapNestedFix::rose>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<LoopifyGapNestedFix::rose>::Cons>(l.v());
        _stack.emplace_back(_after_rose_sum_in_Cons{crane_raw(a10)});
        _stack.emplace_back(_call{&a00});
      }
    } else if (std::holds_alternative<_after_rose_sum_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_rose_sum_in_Cons>(_popped));
      _stack.pop_back();
      const List<LoopifyGapNestedFix::rose> &a10 = *_f.a10;
      _stack.emplace_back(_after_sum_list_in_Cons{_result});
      _stack.emplace_back(_call_sum_list{&a10});
    } else if (std::holds_alternative<_after_sum_list_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_sum_list_in_Cons>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + _result);
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Rose0>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyGapNestedFix::rose_sum_sample() {
  return rose_sum(sample_tree);
}
