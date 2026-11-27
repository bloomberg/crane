#include "loopify_decltype.h"

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
uint64_t LoopifyDecltype::count_true(const List<bool> &xs) {
  // Explicit stack replaces the non-tail recursion of count_true: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<bool> *xs;
  };

  struct _after_count_true_in_Cons {
    bool a0;
  };

  using _frame = std::variant<_call, _after_count_true_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&xs});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<bool> &xs = *_f.xs;
      if (std::holds_alternative<typename List<bool>::Nil>(xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<bool>::Cons>(xs.v());
        _stack.emplace_back(_after_count_true_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_count_true_in_Cons>(_popped));
      _stack.pop_back();
      bool a0 = _f.a0;
      _result = (a0 ? UINT64_C(1) : UINT64_C(0)) + _result;
    }
  }
  return _result;
}

uint64_t LoopifyDecltype::sum_flagged(const List<LoopifyDecltype::item> &xs) {
  // Explicit stack replaces the non-tail recursion of sum_flagged: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<LoopifyDecltype::item> *xs;
  };

  struct _after_sum_flagged_in_Cons {
    LoopifyDecltype::item a0;
  };

  using _frame = std::variant<_call, _after_sum_flagged_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&xs});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<LoopifyDecltype::item> &xs = *_f.xs;
      if (std::holds_alternative<typename List<LoopifyDecltype::item>::Nil>(
              xs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyDecltype::item>::Cons>(xs.v());
        _stack.emplace_back(_after_sum_flagged_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_flagged_in_Cons>(_popped));
      _stack.pop_back();
      LoopifyDecltype::item a0 = std::move(_f.a0);
      _result = (a0.item_flag ? a0.item_val : UINT64_C(0)) + _result;
    }
  }
  return _result;
}
