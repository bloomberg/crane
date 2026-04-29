#include <loopify_match_arg.h>

/// Count the number of Dot cells in a list.
/// The match on c inside the Cons branch triggers bug 2.
__attribute__((pure)) unsigned int
LoopifyMatchArg::count_dots(const List<LoopifyMatchArg::Cell> &xs) {
  struct _Enter {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&xs});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyMatchArg::Cell> &xs = *(_f.xs);
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        switch (d_a0) {
        case Cell::e_DOT: {
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
        default: {
          _stack.emplace_back(_Enter{d_a1.get()});
        }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// A plain recursive length — triggers bug 1 (missing <vector>)
/// when loopify converts it to an explicit-stack loop.
__attribute__((pure)) unsigned int
LoopifyMatchArg::my_length(const List<LoopifyMatchArg::Cell> &xs) {
  struct _Enter {
    const List<LoopifyMatchArg::Cell> *xs;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&xs});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyMatchArg::Cell> &xs = *(_f.xs);
      if (std::holds_alternative<typename List<LoopifyMatchArg::Cell>::Nil>(
              xs.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyMatchArg::Cell>::Cons>(xs.v());
        _stack.emplace_back(_Call1{1u});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
