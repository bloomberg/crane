#include "loopify_decltype.h"

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
unsigned int LoopifyDecltype::count_true(
    const List<bool>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<bool> *xs;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&xs});
  /// Loopified count_true: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<bool> &xs = *_f.xs;
      if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
        _stack.emplace_back(_Resume_Cons{(a0 ? 1u : 0u)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyDecltype::sum_flagged(
    const List<LoopifyDecltype::item>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyDecltype::item> *xs;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&xs});
  /// Loopified sum_flagged: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyDecltype::item> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyDecltype::item>::Nil>(
              xs.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyDecltype::item>::Cons>(xs.v());
        _stack.emplace_back(_Resume_Cons{(a0.item_flag ? a0.item_val : 0u)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
