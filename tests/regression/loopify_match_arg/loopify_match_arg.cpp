#include "loopify_match_arg.h"

/// Count the number of Dot cells in a list.
/// The match on c inside the Cons branch triggers bug 2.
uint64_t LoopifyMatchArg::count_dots(const List<LoopifyMatchArg::Cell> &xs) {
  // Explicit stack replaces the non-tail recursion of count_dots: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  struct _after_count_dots_in_Cons {};

  using _frame = std::variant<_call, _after_count_dots_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&xs});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<LoopifyMatchArg::Cell> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        switch (a0) {
        case Cell::DOT: {
          _stack.emplace_back(_after_count_dots_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
          break;
        }
        default: {
          _stack.emplace_back(_call{crane_raw(a1)});
        }
        }
      }
    } else {
      auto _f = std::move(std::get<_after_count_dots_in_Cons>(_popped));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

/// A plain recursive length — triggers bug 1 (missing <vector>)
/// when loopify converts it to an explicit-stack loop.
uint64_t LoopifyMatchArg::my_length(const List<LoopifyMatchArg::Cell> &xs) {
  // Explicit stack replaces the non-tail recursion of my_length: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  struct _after_my_length_in_Cons {};

  using _frame = std::variant<_call, _after_my_length_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&xs});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<LoopifyMatchArg::Cell> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        _stack.emplace_back(_after_my_length_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_my_length_in_Cons>(_popped));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}
