#include "loopify_match_arg.h"

/// Count the number of Dot cells in a list.
/// The match on c inside the Cons branch triggers bug 2.
uint64_t LoopifyMatchArg::count_dots(
    const List<LoopifyMatchArg::Cell>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&xs});
  /// Loopified count_dots: _Enter -> _Resume_Cons.
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
          _stack.emplace_back(_Resume_Cons{UINT64_C(1)});
          _stack.emplace_back(_Enter{a1.get()});
        } break;
        default: {
          _stack.emplace_back(_Enter{a1.get()});
        }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
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

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&xs});
  /// Loopified my_length: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{UINT64_C(1)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
