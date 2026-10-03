#include "loopify_decltype.h"

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
uint64_t LoopifyDecltype::count_true(
    const List<bool>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<bool> *xs;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    bool a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&xs});
  /// Loopified count_true: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<bool> &xs = *_f.xs;
      if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      bool a0 = _f.a0;
      _result = ((a0 ? UINT64_C(1) : UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyDecltype::sum_flagged(
    const List<LoopifyDecltype::item>
        &xs) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyDecltype::item> *xs;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    LoopifyDecltype::item a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&xs});
  /// Loopified sum_flagged: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyDecltype::item> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyDecltype::item>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyDecltype::item>::Cons>(xs.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      LoopifyDecltype::item a0 = std::move(_f.a0);
      _result =
          ((a0.item_flag ? a0.item_val : UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}
