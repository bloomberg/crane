#include "loopify_nested_calls.h"

/// Shape 1: a let-bound compound expression computed after the recursive
/// call.  The generated continuation frame is pushed with a variable
/// (here) that is only declared and computed later, inside the
/// continuation branch: C++ compile error.
uint64_t sum_signum(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of sum_signum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_sum_signum_in_S {
    uint64_t n_;
  };

  using _frame = std::variant<_call, _after_sum_signum_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_sum_signum_in_S{n_});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_signum_in_S>(_popped));
      _stack.pop_back();
      uint64_t n_ = _f.n_;
      uint64_t here;
      if (n_ == UINT64_C(0)) {
        here = UINT64_C(0);
      } else {
        here = UINT64_C(1);
      }
      _result = (_result + here);
    }
  }
  return _result;
}

/// Shape 2: a recursive call under a conditional inside a let.  The
/// generated continuation branch assigns to a variable (rest) declared in
/// a different scope, and the consumer of rest runs before the recursive
/// frame is processed: C++ compile error, and wrong scheduling besides.
///
/// down_let n computes n-1; n-2; ...; 0: for example,
/// down_let 3 = [2; 1; 0].
List<uint64_t> down_let(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of down_let: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_down_let_in_false {
    uint64_t n_;
  };

  using _frame = std::variant<_call, _after_down_let_in_false>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        List<uint64_t> rest;
        if (n_ == UINT64_C(0)) {
          rest = List<uint64_t>::nil();
          {
            _result = List<uint64_t>::cons(n_, std::move(rest));
          }
        } else {
          _stack.emplace_back(_after_down_let_in_false{n_});
          _stack.emplace_back(_call{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_down_let_in_false>(_popped));
      _stack.pop_back();
      uint64_t n_ = _f.n_;
      auto rest = std::move(_result);
      _result = List<uint64_t>::cons(n_, std::move(rest));
    }
  }
  return _result;
}

/// Shape 3: the same function as shape 2 with the let inlined, so the
/// recursive call sits under a conditional inside a constructor argument.
/// This one compiles, but the generated loop drops the cons entirely:
/// down_inline 3 equals [2; 1; 0] in Rocq, yet extracts to code that
/// returns .  Plain cons n' (down_inline n') with the recursive call
/// directly in argument position is handled correctly.
List<uint64_t> down_inline(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of down_inline: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_down_inline_in_false {
    uint64_t n_;
  };

  using _frame = std::variant<_call, _after_down_inline_in_false>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        List<uint64_t> _tmp1;
        if (n_ == UINT64_C(0)) {
          _tmp1 = List<uint64_t>::nil();
          {
            _result = List<uint64_t>::cons(n_, std::move(_tmp1));
          }
        } else {
          _stack.emplace_back(_after_down_inline_in_false{n_});
          _stack.emplace_back(_call{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_down_inline_in_false>(_popped));
      _stack.pop_back();
      uint64_t n_ = _f.n_;
      _result = List<uint64_t>::cons(n_, std::move(_result));
    }
  }
  return _result;
}
