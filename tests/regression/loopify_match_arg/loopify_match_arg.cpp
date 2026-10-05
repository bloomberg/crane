#include "loopify_match_arg.h"

/// Count the number of Dot cells in a list.
/// The match on c inside the Cons branch triggers bug 2.
uint64_t
LoopifyMatchArg::count_dots(const List<LoopifyMatchArg::Cell>
                                &xs) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&xs});
  /// Loopified count_dots: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<LoopifyMatchArg::Cell> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        switch (a0) {
        case Cell::DOT: {
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
          break;
        }
        default: {
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

/// A plain recursive length — triggers bug 1 (missing <vector>)
/// when loopify converts it to an explicit-stack loop.
uint64_t LoopifyMatchArg::my_length(const List<LoopifyMatchArg::Cell> &xs) {
  {
    const List<LoopifyMatchArg::Cell> &_lc1_l = xs;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<LoopifyMatchArg::Cell> *_lc1_loop_l = &_lc1_l;
    while (true) {
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              _lc1_loop_l->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(
                _lc1_loop_l->v());
        _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
        _lc1_loop_l = crane_raw(a1);
      }
    }
  }
}
