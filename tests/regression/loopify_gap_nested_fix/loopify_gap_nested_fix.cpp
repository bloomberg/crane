#include "loopify_gap_nested_fix.h"

uint64_t LoopifyGapNestedFix::rose_sum(
    const LoopifyGapNestedFix::rose
        &r) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyGapNestedFix::rose r;
  };

  /// _Enter_sum_list: captures varying parameters for each recursive call.
  struct _Enter_sum_list {
    List<LoopifyGapNestedFix::rose> l;
  };

  /// _Cont_Cons: saves [a10], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    std::shared_ptr<List<LoopifyGapNestedFix::rose>> a10;
  };

  /// _Cont_Cons_1: saves [_tmp2], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons_1 {
    uint64_t _tmp2;
  };

  /// _Cont_Rose0: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Rose0 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Enter_sum_list, _Cont_Cons, _Cont_Cons_1,
                              _Cont_Rose0>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{r});
  /// Loopified rose_sum: _Enter -> _Cont_Cons -> _Cont_Cons_1 -> _Cont_Rose0.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyGapNestedFix::rose &r = std::move(_f.r);
      const auto &[a0, a1] =
          std::get<typename LoopifyGapNestedFix::rose::Rose0>(r.v());
      uint64_t _tmp3;
      {
      }
      {
      }
      _stack.emplace_back(_Cont_Rose0{a0});
      _stack.emplace_back(_Enter_sum_list{*a1});
    } else if (std::holds_alternative<_Enter_sum_list>(_frame)) {
      auto _f = std::move(std::get<_Enter_sum_list>(_frame));
      const List<LoopifyGapNestedFix::rose> &l = std::move(_f.l);
      if (std::holds_alternative<typename List<LoopifyGapNestedFix::rose>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<LoopifyGapNestedFix::rose>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a10});
        _stack.emplace_back(_Enter{a00});
      }
    } else if (std::holds_alternative<_Cont_Cons>(_frame)) {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      std::shared_ptr<List<LoopifyGapNestedFix::rose>> a10 = std::move(_f.a10);
      _stack.emplace_back(_Cont_Cons_1{std::move(_result)});
      _stack.emplace_back(_Enter_sum_list{*a10});
    } else if (std::holds_alternative<_Cont_Cons_1>(_frame)) {
      auto _f = std::move(std::get<_Cont_Cons_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    } else {
      auto _f = std::move(std::get<_Cont_Rose0>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyGapNestedFix::rose_sum_sample(std::monostate) {
  return rose_sum(sample_tree);
}
