#include "loopify_match_arg.h"

/// Count the number of Dot cells in a list.
/// The match on c inside the Cons branch triggers bug 2.
uint64_t LoopifyMatchArg::count_dots(
    const List<LoopifyMatchArg::Cell>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  /// _Cont_Cons: resumes after recursive call, then processes rest.
  struct _Cont_Cons {};

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&xs});
  /// Loopified count_dots: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyMatchArg::Cell> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        switch (a0) {
        case Cell::DOT: {
          _stack.emplace_back(_Cont_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
          break;
        }
        default: {
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t r_ = std::move(_result);
      _result = (UINT64_C(1) + r_);
    }
  }
  return _result;
}

/// A plain recursive length — triggers bug 1 (missing <vector>)
/// when loopify converts it to an explicit-stack loop.
uint64_t LoopifyMatchArg::my_length(
    const List<LoopifyMatchArg::Cell>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  /// _Cont_Cons: resumes after recursive call, then processes rest.
  struct _Cont_Cons {};

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&xs});
  /// Loopified my_length: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyMatchArg::Cell> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        _stack.emplace_back(_Cont_Cons{});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t r_ = std::move(_result);
      _result = (UINT64_C(1) + r_);
    }
  }
  return _result;
}
