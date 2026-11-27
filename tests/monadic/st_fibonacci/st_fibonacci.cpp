#include "st_fibonacci.h"

uint64_t STFibonacci::fib_ST(uint64_t n) {
  if (n < UINT64_C(2)) {
    return n;
  } else {
    uint64_t x = UINT64_C(0);
    uint64_t y = UINT64_C(1);
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    while (true) {
      if (n <= 0) {
        return x;
      } else {
        uint64_t k_ = n - 1;
        uint64_t x_ = x;
        x = y;
        y = (x_ + y);
        n = k_;
      }
    }
  }
}

uint64_t STFibonacci::fib_fun(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of fib_fun: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_fib_fun_in_S {
    uint64_t m;
  };

  struct _after_fib_fun_in_S_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_fib_fun_in_S, _after_fib_fun_in_S_2>;
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
        uint64_t m0 = n - 1;
        if (m0 <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = m0 - 1;
          _stack.emplace_back(_after_fib_fun_in_S{m});
          _stack.emplace_back(_call{m0});
        }
      }
    } else if (std::holds_alternative<_after_fib_fun_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_fib_fun_in_S>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      _stack.emplace_back(_after_fib_fun_in_S_2{_result});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_fib_fun_in_S_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}
