#include "loopify_gap_nested_fix.h"

uint64_t
LoopifyGapNestedFix::rose_sum(const LoopifyGapNestedFix::rose
                                  &r) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    LoopifyGapNestedFix::rose r;
  };

  /// CraneEnter_sum_list: captures varying parameters for each recursive call.
  struct CraneEnter_sum_list {
    List<LoopifyGapNestedFix::rose> l;
  };

  /// CraneCont_Cons: saves [a10], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    std::shared_ptr<List<LoopifyGapNestedFix::rose>> a10;
  };

  /// CraneCont_Cons_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    uint64_t _tmp2;
  };

  /// CraneCont_Rose0: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Rose0 {
    uint64_t a0;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneEnter_sum_list, CraneCont_Cons,
                   CraneCont_Cons_1, CraneCont_Rose0>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{r});
  /// Loopified rose_sum: CraneEnter -> CraneCont_Cons -> CraneCont_Cons_1 ->
  /// CraneCont_Rose0.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyGapNestedFix::rose &r = std::move(_f.r);
      const auto &[a0, a1] =
          std::get<typename LoopifyGapNestedFix::rose::Rose0>(r.v());
      uint64_t _tmp3;
      {
      }
      {
      }
      _stack.emplace_back(CraneCont_Rose0{a0});
      _stack.emplace_back(CraneEnter_sum_list{*a1});
    } else if (std::holds_alternative<CraneEnter_sum_list>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_sum_list>(_frame));
      const List<LoopifyGapNestedFix::rose> &l = std::move(_f.l);
      if (std::holds_alternative<typename List<LoopifyGapNestedFix::rose>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<LoopifyGapNestedFix::rose>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a10});
        _stack.emplace_back(CraneEnter{a00});
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      std::shared_ptr<List<LoopifyGapNestedFix::rose>> a10 = std::move(_f.a10);
      _stack.emplace_back(CraneCont_Cons_1{std::move(_result)});
      _stack.emplace_back(CraneEnter_sum_list{*a10});
    } else if (std::holds_alternative<CraneCont_Cons_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_Rose0>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyGapNestedFix::rose_sum_sample(std::monostate) {
  return rose_sum(sample_tree);
}
