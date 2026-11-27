#include "loopify_classics.h"

uint64_t LoopifyClassics::factorial(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of factorial: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_factorial_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_factorial_in_S>;
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
        _result = UINT64_C(1);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_factorial_in_S{n});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_factorial_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = n * _result;
    }
  }
  return _result;
}

uint64_t LoopifyClassics::fib(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of fib: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_fib_in_S {
    uint64_t n_p;
  };

  struct _after_fib_in_S_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_fib_in_S, _after_fib_in_S_2>;
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
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n_p = n_ - 1;
          _stack.emplace_back(_after_fib_in_S{n_p});
          _stack.emplace_back(_call{n_});
        }
      }
    } else if (std::holds_alternative<_after_fib_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_fib_in_S>(_popped));
      _stack.pop_back();
      uint64_t n_p = _f.n_p;
      _stack.emplace_back(_after_fib_in_S_2{_result});
      _stack.emplace_back(_call{n_p});
    } else {
      auto _f = std::move(std::get<_after_fib_in_S_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyClassics::ack_fuel(uint64_t fuel, uint64_t m, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of ack_fuel: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t m;
    uint64_t fuel;
  };

  struct _after_ack_fuel_in_false {
    uint64_t m;
    uint64_t fuel_;
  };

  using _frame = std::variant<_call, _after_ack_fuel_in_false>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, m, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t m = _f.m;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = n + UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (m == UINT64_C(0)) {
          _result = n + UINT64_C(1);
        } else if (n == UINT64_C(0)) {
          _stack.emplace_back(_call{
              UINT64_C(1), (m - UINT64_C(1) > m ? 0 : m - UINT64_C(1)), fuel_});
        } else {
          _stack.emplace_back(_after_ack_fuel_in_false{m, fuel_});
          _stack.emplace_back(
              _call{(n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), m, fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_ack_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(
          _call{_result, (m - UINT64_C(1) > m ? 0 : m - UINT64_C(1)), fuel_});
    }
  }
  return _result;
}

uint64_t LoopifyClassics::ack(uint64_t m, uint64_t n) {
  return ack_fuel(UINT64_C(100) * (m + UINT64_C(1)) * (n + UINT64_C(1)), m, n);
}

uint64_t LoopifyClassics::binomial_fuel(uint64_t fuel, uint64_t n, uint64_t k) {
  // Explicit stack replaces the non-tail recursion of binomial_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t k;
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_binomial_fuel_in_false {
    uint64_t n;
    uint64_t k;
    uint64_t fuel_;
  };

  struct _after_binomial_fuel_in_false_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_binomial_fuel_in_false,
                              _after_binomial_fuel_in_false_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k, n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (((k == UINT64_C(0)) || (k == n))) {
          _result = UINT64_C(1);
        } else {
          _stack.emplace_back(_after_binomial_fuel_in_false{n, k, fuel_});
          _stack.emplace_back(
              _call{(k - UINT64_C(1) > k ? 0 : k - UINT64_C(1)),
                    (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), fuel_});
        }
      }
    } else if (std::holds_alternative<_after_binomial_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_binomial_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t k = _f.k;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(_after_binomial_fuel_in_false_2{_result});
      _stack.emplace_back(
          _call{k, (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)), fuel_});
    } else {
      auto _f = std::move(std::get<_after_binomial_fuel_in_false_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyClassics::binomial(uint64_t n, uint64_t k) {
  return binomial_fuel(n * k, n, k);
}

uint64_t LoopifyClassics::pascal_fuel(uint64_t fuel, uint64_t row,
                                      uint64_t col) {
  return binomial_fuel(fuel, row, col);
}

uint64_t LoopifyClassics::pascal(uint64_t row, uint64_t col) {
  return pascal_fuel(row * col, row, col);
}

uint64_t LoopifyClassics::gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (fuel <= 0) {
      return a;
    } else {
      uint64_t fuel_ = fuel - 1;
      if (b == UINT64_C(0)) {
        return a;
      } else {
        uint64_t _next_b = (b ? a % b : a);
        uint64_t _next_a = b;
        fuel = fuel_;
        b = _next_b;
        a = _next_a;
      }
    }
  }
}

uint64_t LoopifyClassics::gcd(uint64_t a, uint64_t b) {
  return gcd_fuel(a + b, a, b);
}

uint64_t LoopifyClassics::power(uint64_t base, uint64_t exp) {
  // Explicit stack replaces the non-tail recursion of power: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t exp;
  };

  struct _after_power_in_S {};

  using _frame = std::variant<_call, _after_power_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{exp});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t exp = _f.exp;
      if (exp <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t exp_ = exp - 1;
        _stack.emplace_back(_after_power_in_S{});
        _stack.emplace_back(_call{exp_});
      }
    } else {
      auto _f = std::move(std::get<_after_power_in_S>(_popped));
      _stack.pop_back();
      _result = base * _result;
    }
  }
  return _result;
}

uint64_t LoopifyClassics::sum_to(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of sum_to: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_sum_to_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_sum_to_in_S>;
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
        _stack.emplace_back(_after_sum_to_in_S{n});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_to_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = n + _result;
    }
  }
  return _result;
}

uint64_t LoopifyClassics::sum_squares(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of sum_squares: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_sum_squares_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_sum_squares_in_S>;
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
        _stack.emplace_back(_after_sum_squares_in_S{n});
        _stack.emplace_back(_call{n_});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_squares_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = n * n + _result;
    }
  }
  return _result;
}
