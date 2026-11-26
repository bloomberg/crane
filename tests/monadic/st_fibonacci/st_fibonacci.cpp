#include "st_fibonacci.h"

uint64_t StFibonacci::fib_ST(uint64_t n) {
  if (n < UINT64_C(2)) {
    return n;
  } else {
    std::shared_ptr<uint64_t> x = std::make_shared<uint64_t>(UINT64_C(0));
    std::shared_ptr<uint64_t> y = std::make_shared<uint64_t>(UINT64_C(1));
    auto fib_loop =
        [](uint64_t k, const std::shared_ptr<uint64_t> &x0,
           const std::shared_ptr<uint64_t> &y0)
             -> uint64_t {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          uint64_t _loop_k = k;
          while (true) {
            if (_loop_k <= 0) {
              return *x0.get();
            } else {
              uint64_t k_ = _loop_k - 1;
              uint64_t x_ = *x0.get();
              uint64_t y_ = *y0.get();
              *x0.get() = y_;
              *y0.get() = (x_ + y_);
              _loop_k = k_;
            }
          }
        };
    return fib_loop(n, std::move(x), std::move(y));
  }
}

uint64_t StFibonacci::fib_fun(uint64_t n) {
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
      _stack.emplace_back(_after_fib_fun_in_S_2{std::move(_result)});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_fib_fun_in_S_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}
