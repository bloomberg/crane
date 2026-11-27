#include "loopify_numbers.h"

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
uint64_t LoopifyNumbers::factorial(uint64_t n) {
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
        uint64_t m = n - 1;
        _stack.emplace_back(_after_factorial_in_S{n});
        _stack.emplace_back(_call{m});
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

uint64_t LoopifyNumbers::fib(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of fib: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_fib_in_S {
    uint64_t m;
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
          uint64_t m = n_ - 1;
          _stack.emplace_back(_after_fib_in_S{m});
          _stack.emplace_back(_call{n_});
        }
      }
    } else if (std::holds_alternative<_after_fib_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_fib_in_S>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      _stack.emplace_back(_after_fib_in_S_2{_result});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_fib_in_S_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::tribonacci_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of tribonacci_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_tribonacci_fuel_in_S {
    uint64_t f;
    uint64_t m;
  };

  struct _after_tribonacci_fuel_in_S_2 {
    uint64_t f;
    uint64_t m;
    uint64_t _tmp3;
  };

  struct _after_tribonacci_fuel_in_S_3 {
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_tribonacci_fuel_in_S,
                              _after_tribonacci_fuel_in_S_2,
                              _after_tribonacci_fuel_in_S_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t n0 = n - 1;
          if (n0 <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t n1 = n0 - 1;
            if (n1 <= 0) {
              _result = UINT64_C(1);
            } else {
              uint64_t m = n1 - 1;
              _stack.emplace_back(_after_tribonacci_fuel_in_S{f, m});
              _stack.emplace_back(_call{((m + 1) + 1), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_after_tribonacci_fuel_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_tribonacci_fuel_in_S>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(_after_tribonacci_fuel_in_S_2{f, m, _result});
      _stack.emplace_back(_call{(m + 1), f});
    } else if (std::holds_alternative<_after_tribonacci_fuel_in_S_2>(_popped)) {
      auto _f = std::move(std::get<_after_tribonacci_fuel_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(_after_tribonacci_fuel_in_S_3{_f._tmp3, _result});
      _stack.emplace_back(_call{m, f});
    } else {
      auto _f = std::move(std::get<_after_tribonacci_fuel_in_S_3>(_popped));
      _stack.pop_back();
      _result = _f._tmp3 + (_f._tmp2 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::tribonacci(uint64_t n) {
  return tribonacci_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (fuel <= 0) {
      return a;
    } else {
      uint64_t f = fuel - 1;
      if (b <= 0) {
        return a;
      } else {
        uint64_t _x = b - 1;
        uint64_t _next_b = (b ? a % b : a);
        uint64_t _next_a = b;
        fuel = f;
        b = _next_b;
        a = _next_a;
      }
    }
  }
}

uint64_t LoopifyNumbers::gcd(uint64_t a, uint64_t b) {
  return gcd_fuel(a + b, a, b);
}

uint64_t LoopifyNumbers::binomial(uint64_t n, uint64_t k) {
  // Explicit stack replaces the non-tail recursion of binomial: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t k;
    uint64_t n;
  };

  struct _after_binomial_in_S {
    uint64_t k;
    uint64_t n_;
  };

  struct _after_binomial_in_S_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_binomial_in_S, _after_binomial_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k, n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      uint64_t n = _f.n;
      if (n <= 0) {
        if (k <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t _x = k - 1;
          _result = UINT64_C(0);
        }
      } else {
        uint64_t n_ = n - 1;
        if (k <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t k_ = k - 1;
          _stack.emplace_back(_after_binomial_in_S{k, n_});
          _stack.emplace_back(_call{k_, n_});
        }
      }
    } else if (std::holds_alternative<_after_binomial_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_binomial_in_S>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_binomial_in_S_2{_result});
      _stack.emplace_back(_call{k, n_});
    } else {
      auto _f = std::move(std::get<_after_binomial_in_S_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::pascal(uint64_t row, uint64_t col) {
  // Explicit stack replaces the non-tail recursion of pascal: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t col;
    uint64_t row;
  };

  struct _after_pascal_in_S {
    uint64_t c;
    uint64_t r;
  };

  struct _after_pascal_in_S_2 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_pascal_in_S, _after_pascal_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{col, row});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t col = _f.col;
      uint64_t row = _f.row;
      if (col <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t c = col - 1;
        if (row <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t r = row - 1;
          _stack.emplace_back(_after_pascal_in_S{c, r});
          _stack.emplace_back(_call{c, r});
        }
      }
    } else if (std::holds_alternative<_after_pascal_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_pascal_in_S>(_popped));
      _stack.pop_back();
      uint64_t c = _f.c;
      uint64_t r = _f.r;
      _stack.emplace_back(_after_pascal_in_S_2{_result});
      _stack.emplace_back(_call{(c + 1), r});
    } else {
      auto _f = std::move(std::get<_after_pascal_in_S_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::ackermann_fuel(uint64_t fuel, uint64_t m, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of ackermann_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t m;
    uint64_t fuel;
  };

  struct _after_ackermann_fuel_in_S {
    uint64_t f;
    uint64_t m_;
  };

  using _frame = std::variant<_call, _after_ackermann_fuel_in_S>;
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
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (m <= 0) {
          _result = (n + 1);
        } else {
          uint64_t m_ = m - 1;
          if (n <= 0) {
            _stack.emplace_back(_call{UINT64_C(1), m_, f});
          } else {
            uint64_t n_ = n - 1;
            _stack.emplace_back(_after_ackermann_fuel_in_S{f, m_});
            _stack.emplace_back(_call{n_, m, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_after_ackermann_fuel_in_S>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m_ = _f.m_;
      _stack.emplace_back(_call{_result, m_, f});
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::ack(uint64_t m, uint64_t n) {
  return ackermann_fuel(UINT64_C(1000), m, n);
}

uint64_t LoopifyNumbers::collatz_length_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of collatz_length_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_collatz_length_fuel_in_false {};

  struct _after_collatz_length_fuel_in_true {};

  using _frame = std::variant<_call, _after_collatz_length_fuel_in_false,
                              _after_collatz_length_fuel_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n == UINT64_C(1)) {
          _result = UINT64_C(0);
        } else if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
          _stack.emplace_back(_after_collatz_length_fuel_in_true{});
          _stack.emplace_back(_call{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
        } else {
          _stack.emplace_back(_after_collatz_length_fuel_in_false{});
          _stack.emplace_back(_call{UINT64_C(3) * n + UINT64_C(1), f});
        }
      }
    } else if (std::holds_alternative<_after_collatz_length_fuel_in_false>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_collatz_length_fuel_in_false>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    } else {
      auto _f =
          std::move(std::get<_after_collatz_length_fuel_in_true>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::collatz_length(uint64_t n) {
  return collatz_length_fuel(UINT64_C(1000), n);
}

uint64_t LoopifyNumbers::digitsum_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of digitsum_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_digitsum_fuel_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_digitsum_fuel_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t _x = n - 1;
          _stack.emplace_back(_after_digitsum_fuel_in_S{n});
          _stack.emplace_back(_call{(UINT64_C(10) ? n / UINT64_C(10) : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_digitsum_fuel_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = (UINT64_C(10) ? n % UINT64_C(10) : n) + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::digitsum(uint64_t n) {
  return digitsum_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::dec_to_bin_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of dec_to_bin_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_dec_to_bin_fuel_in_S {
    uint64_t digit;
  };

  using _frame = std::variant<_call, _after_dec_to_bin_fuel_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t _x = n - 1;
          uint64_t digit = (UINT64_C(2) ? n % UINT64_C(2) : n);
          _stack.emplace_back(_after_dec_to_bin_fuel_in_S{digit});
          _stack.emplace_back(_call{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_dec_to_bin_fuel_in_S>(_popped));
      _stack.pop_back();
      uint64_t digit = _f.digit;
      _result = digit + UINT64_C(10) * _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::dec_to_bin(uint64_t n) {
  return dec_to_bin_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::sum_to(uint64_t n) {
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
        uint64_t m = n - 1;
        _stack.emplace_back(_after_sum_to_in_S{n});
        _stack.emplace_back(_call{m});
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

uint64_t LoopifyNumbers::sum_squares(uint64_t n) {
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
        uint64_t m = n - 1;
        _stack.emplace_back(_after_sum_squares_in_S{n});
        _stack.emplace_back(_call{m});
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

uint64_t LoopifyNumbers::alternating_sum(bool sign, uint64_t acc, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return acc;
    } else {
      uint64_t m = n - 1;
      uint64_t new_acc;
      if (sign) {
        new_acc = acc + n;
      } else {
        new_acc = (acc - n > acc ? 0 : acc - n);
      }
      n = m;
      acc = new_acc;
      sign = !(sign);
    }
  }
}

uint64_t LoopifyNumbers::staircase_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of staircase_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_staircase_fuel_in_S {
    uint64_t f;
    uint64_t m;
  };

  struct _after_staircase_fuel_in_S_2 {
    uint64_t f;
    uint64_t m;
    uint64_t _tmp3;
  };

  struct _after_staircase_fuel_in_S_3 {
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_staircase_fuel_in_S,
                   _after_staircase_fuel_in_S_2, _after_staircase_fuel_in_S_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n0 = n - 1;
          if (n0 <= 0) {
            _result = UINT64_C(1);
          } else {
            uint64_t n1 = n0 - 1;
            if (n1 <= 0) {
              _result = UINT64_C(2);
            } else {
              uint64_t m = n1 - 1;
              _stack.emplace_back(_after_staircase_fuel_in_S{f, m});
              _stack.emplace_back(_call{((m + 1) + 1), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_after_staircase_fuel_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_staircase_fuel_in_S>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(_after_staircase_fuel_in_S_2{f, m, _result});
      _stack.emplace_back(_call{(m + 1), f});
    } else if (std::holds_alternative<_after_staircase_fuel_in_S_2>(_popped)) {
      auto _f = std::move(std::get<_after_staircase_fuel_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(_after_staircase_fuel_in_S_3{_f._tmp3, _result});
      _stack.emplace_back(_call{m, f});
    } else {
      auto _f = std::move(std::get<_after_staircase_fuel_in_S_3>(_popped));
      _stack.pop_back();
      _result = _f._tmp3 + (_f._tmp2 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::staircase(uint64_t n) {
  return staircase_fuel(UINT64_C(100), n);
}

/// iterate_pred n applies predecessor n times, starting from n.
/// Tests church-style iteration with concrete function.
uint64_t LoopifyNumbers::iterate_pred(uint64_t n) {
  return church(
      n,
      [](uint64_t x) -> uint64_t {
        if (x <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t m = x - 1;
          return m;
        }
      },
      n);
}

/// sum_while_positive n sums numbers from n down to 0, but only positive ones.
/// Tests conditional accumulation in recursion.
uint64_t LoopifyNumbers::sum_while_positive(uint64_t n) { return sum_to(n); }

/// count_down_by k n counts down from n by steps of k.
/// Tests recursion with non-standard step size.
uint64_t LoopifyNumbers::count_down_by_fuel(uint64_t fuel, uint64_t k,
                                            uint64_t n) {
  // Explicit stack replaces the non-tail recursion of count_down_by_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_count_down_by_fuel_in_false {};

  using _frame = std::variant<_call, _after_count_down_by_fuel_in_false>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t _x = n - 1;
          if (n < k) {
            _result = UINT64_C(1);
          } else {
            _stack.emplace_back(_after_count_down_by_fuel_in_false{});
            _stack.emplace_back(_call{(n - k > n ? 0 : n - k), f});
          }
        }
      }
    } else {
      auto _f =
          std::move(std::get<_after_count_down_by_fuel_in_false>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::count_down_by(uint64_t k, uint64_t n) {
  return count_down_by_fuel(UINT64_C(100), k, n);
}

/// mixed_arith n combines multiplication and addition in recursion.
uint64_t LoopifyNumbers::mixed_arith_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of mixed_arith_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_mixed_arith_fuel_in_S {
    uint64_t f;
    uint64_t m;
  };

  struct _after_mixed_arith_fuel_in_S_2 {
    uint64_t f;
    uint64_t m;
    uint64_t _tmp3;
  };

  struct _after_mixed_arith_fuel_in_S_3 {
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_mixed_arith_fuel_in_S,
                              _after_mixed_arith_fuel_in_S_2,
                              _after_mixed_arith_fuel_in_S_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t f = fuel - 1;
        if (n <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t n0 = n - 1;
          if (n0 <= 0) {
            _result = UINT64_C(1);
          } else {
            uint64_t n_ = n0 - 1;
            if (n_ <= 0) {
              _result = UINT64_C(1);
            } else {
              uint64_t m = n_ - 1;
              _stack.emplace_back(_after_mixed_arith_fuel_in_S{f, m});
              _stack.emplace_back(_call{n_, f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_after_mixed_arith_fuel_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_mixed_arith_fuel_in_S>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(_after_mixed_arith_fuel_in_S_2{f, m, _result});
      _stack.emplace_back(_call{m, f});
    } else if (std::holds_alternative<_after_mixed_arith_fuel_in_S_2>(_popped)) {
      auto _f = std::move(std::get<_after_mixed_arith_fuel_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t f = _f.f;
      uint64_t m = _f.m;
      _stack.emplace_back(_after_mixed_arith_fuel_in_S_3{_f._tmp3, _result});
      _stack.emplace_back(_call{
          (m == UINT64_C(0) ? UINT64_C(0)
                            : (m - UINT64_C(1) > m ? 0 : m - UINT64_C(1))),
          f});
    } else {
      auto _f = std::move(std::get<_after_mixed_arith_fuel_in_S_3>(_popped));
      _stack.pop_back();
      _result = _f._tmp3 * _f._tmp2 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::mixed_arith(uint64_t n) {
  return mixed_arith_fuel(UINT64_C(1000), n);
}

/// is_even n checks if n is even (mutually recursive with is_odd).
bool LoopifyNumbers::is_even_fuel(uint64_t fuel, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (fuel <= 0) {
      return true;
    } else {
      uint64_t f = fuel - 1;
      if (n == UINT64_C(0)) {
        return true;
      } else {
        uint64_t n0 = (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1));
        if (f <= 0) {
          return false;
        } else {
          uint64_t f0 = f - 1;
          if (n0 == UINT64_C(0)) {
            return false;
          } else {
            n = (n0 - UINT64_C(1) > n0 ? 0 : n0 - UINT64_C(1));
            fuel = f0;
          }
        }
      }
    }
  }
}

bool LoopifyNumbers::is_odd_fuel(uint64_t fuel, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (fuel <= 0) {
      return false;
    } else {
      uint64_t f = fuel - 1;
      if (n == UINT64_C(0)) {
        return false;
      } else {
        uint64_t n0 = (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1));
        if (f <= 0) {
          return true;
        } else {
          uint64_t f0 = f - 1;
          if (n0 == UINT64_C(0)) {
            return true;
          } else {
            n = (n0 - UINT64_C(1) > n0 ? 0 : n0 - UINT64_C(1));
            fuel = f0;
          }
        }
      }
    }
  }
}

bool LoopifyNumbers::is_even(uint64_t n) {
  return is_even_fuel(UINT64_C(1000), n);
}

bool LoopifyNumbers::is_odd(uint64_t n) {
  return is_odd_fuel(UINT64_C(1000), n);
}

/// power b e computes b^e.
uint64_t LoopifyNumbers::power(uint64_t b, uint64_t e) {
  // Explicit stack replaces the non-tail recursion of power: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t e;
  };

  struct _after_power_in_S {};

  using _frame = std::variant<_call, _after_power_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{e});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t e = _f.e;
      if (e <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t e_ = e - 1;
        _stack.emplace_back(_after_power_in_S{});
        _stack.emplace_back(_call{e_});
      }
    } else {
      auto _f = std::move(std::get<_after_power_in_S>(_popped));
      _stack.pop_back();
      _result = b * _result;
    }
  }
  return _result;
}

/// power_mod b e m computes (b^e) mod m efficiently.
uint64_t LoopifyNumbers::power_mod_fuel(uint64_t fuel, uint64_t b, uint64_t e,
                                        uint64_t m) {
  // Explicit stack replaces the non-tail recursion of power_mod_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t e;
    uint64_t fuel;
  };

  struct _after_power_mod_fuel_in_false {};

  struct _after_power_mod_fuel_in_true {};

  using _frame = std::variant<_call, _after_power_mod_fuel_in_false,
                              _after_power_mod_fuel_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{e, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t e = _f.e;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (e == UINT64_C(0)) {
          _result = UINT64_C(1);
        } else {
          if ((UINT64_C(2) ? e % UINT64_C(2) : e) == UINT64_C(0)) {
            _stack.emplace_back(_after_power_mod_fuel_in_true{});
          } else {
            _stack.emplace_back(_after_power_mod_fuel_in_false{});
          }
          _stack.emplace_back(_call{(UINT64_C(2) ? e / UINT64_C(2) : 0), f});
        }
      }
    } else if (std::holds_alternative<_after_power_mod_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_power_mod_fuel_in_false>(_popped));
      _stack.pop_back();
      uint64_t half = _result;
      auto _once1 = b * (half * half);
      _result = (m ? _once1 % m : _once1);
    } else {
      auto _f = std::move(std::get<_after_power_mod_fuel_in_true>(_popped));
      _stack.pop_back();
      uint64_t half = _result;
      auto _once2 = half * half;
      _result = (m ? _once2 % m : _once2);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::power_mod(uint64_t b, uint64_t e, uint64_t m) {
  return power_mod_fuel(UINT64_C(1000), b, e, m);
}

/// sum_divisors n sums all divisors of n (excluding n itself).
uint64_t LoopifyNumbers::sum_divisors_aux(uint64_t n, uint64_t k) {
  // Explicit stack replaces the non-tail recursion of sum_divisors_aux: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t k;
  };

  struct _after_sum_divisors_aux_in_true {
    uint64_t k;
  };

  using _frame = std::variant<_call, _after_sum_divisors_aux_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      if (k <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t k_ = k - 1;
        if (k_ <= 0) {
          _result = UINT64_C(0);
        } else {
          uint64_t _x = k_ - 1;
          if ((k ? n % k : n) == UINT64_C(0)) {
            _stack.emplace_back(_after_sum_divisors_aux_in_true{k});
          }
          _stack.emplace_back(_call{k_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_sum_divisors_aux_in_true>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      _result = k + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_divisors(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    if (n_ <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t _x = n_ - 1;
      return sum_divisors_aux(n_,
                              (n_ - UINT64_C(1) > n_ ? 0 : n_ - UINT64_C(1)));
    }
  }
}

/// sum_odd_indices l and sum_even_indices l are mutually recursive.
/// sum_odd_indices adds elements at odd positions (0, 2, 4...).
/// sum_even_indices processes even positions (1, 3, 5...) by calling
/// sum_odd_indices.
uint64_t LoopifyNumbers::sum_odd_indices_fuel(uint64_t fuel,
                                              const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_odd_indices_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  struct _call_sum_even_indices_fuel_entry {
    const List<uint64_t> *l0;
    uint64_t fuel0;
  };

  struct _after_sum_even_indices_fuel_entry_in_Cons {
    uint64_t a00;
  };

  using _frame = std::variant<_call, _call_sum_even_indices_fuel_entry,
                              _after_sum_even_indices_fuel_entry_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_after_sum_even_indices_fuel_entry_in_Cons{a00});
          _stack.emplace_back(
              _call_sum_even_indices_fuel_entry{crane_raw(a10), f});
        }
      }
    } else if (
            std::holds_alternative<_call_sum_even_indices_fuel_entry>(_popped)) {
      auto _f = std::move(std::get<_call_sum_even_indices_fuel_entry>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l0 = *_f.l0;
      uint64_t fuel0 = _f.fuel0;
      if (fuel0 <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel0 - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l0.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l0.v());
          _stack.emplace_back(_call{crane_raw(a1), f});
        }
      }
    } else {
      auto _f = std::move(
          std::get<_after_sum_even_indices_fuel_entry_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = a00 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_even_indices_fuel(uint64_t fuel,
                                               const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_even_indices_fuel:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  struct _after_sum_even_indices_fuel_in_Cons {
    uint64_t a00;
  };

  using _frame = std::variant<_call, _after_sum_even_indices_fuel_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (f <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t f0 = f - 1;
            auto &&_sv0 = *a1;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
              _result = UINT64_C(0);
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(_sv0.v());
              _stack.emplace_back(_after_sum_even_indices_fuel_in_Cons{a00});
              _stack.emplace_back(_call{crane_raw(a10), f0});
            }
          }
        }
      }
    } else {
      auto _f =
          std::move(std::get<_after_sum_even_indices_fuel_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a00 = _f.a00;
      _result = a00 + _result;
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_odd_indices(const List<uint64_t> &l) {
  return sum_odd_indices_fuel(l.length(), l);
}

uint64_t LoopifyNumbers::sum_even_indices(const List<uint64_t> &l) {
  return sum_even_indices_fuel(l.length(), l);
}

/// collatz_list n generates collatz sequence as a list.
List<uint64_t> LoopifyNumbers::collatz_list_fuel(uint64_t fuel, uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t f = fuel - 1;
      if (n == UINT64_C(1)) {
        auto _value = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
        auto _cell = typename List<uint64_t>::Cons(n, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        n = (UINT64_C(2) ? n / UINT64_C(2) : 0);
        fuel = f;
        continue;
      } else if ((UINT64_C(3) ? n % UINT64_C(3) : n) == UINT64_C(0)) {
        auto _cell = typename List<uint64_t>::Cons(n, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        n = (UINT64_C(3) ? n / UINT64_C(3) : 0);
        fuel = f;
        continue;
      } else {
        auto _cell = typename List<uint64_t>::Cons(n, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        n = UINT64_C(3) * n + UINT64_C(1);
        fuel = f;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyNumbers::collatz_list(uint64_t n) {
  return collatz_list_fuel(UINT64_C(1000), n);
}

/// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
uint64_t LoopifyNumbers::sum_divisible_by(uint64_t k, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of sum_divisible_by: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_sum_divisible_by_in_true {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_sum_divisible_by_in_true>;
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
        uint64_t m = n - 1;
        if ((k ? n % k : n) == UINT64_C(0)) {
          _stack.emplace_back(_after_sum_divisible_by_in_true{n});
        }
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_divisible_by_in_true>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = n + _result;
    }
  }
  return _result;
}
