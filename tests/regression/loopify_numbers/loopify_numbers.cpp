#include "loopify_numbers.h"

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
uint64_t
LoopifyNumbers::factorial(uint64_t n) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified factorial: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f.n * _result);
    }
  }
  return _result;
}

uint64_t
LoopifyNumbers::fib(uint64_t n) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_m: saves [n_], dispatches next recursive call.
  struct _After_m {
    uint64_t n_;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_m, _Combine_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified fib: _Enter -> _After_m -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        if (n_ <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = n_ - 1;
          _stack.emplace_back(_After_m{n_});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_Combine_m{_result});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::tribonacci_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After_m: saves [m, f_0, _s2, f_1], dispatches next recursive call.
  struct _After_m {
    uint64_t m;
    uint64_t f_0;
    uint64_t _s2;
    uint64_t f_1;
  };

  /// _After_m_1: saves [_result, _s1, f], dispatches next recursive call.
  struct _After_m_1 {
    uint64_t _result;
    uint64_t _s1;
    uint64_t f;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result_0;
    uint64_t _result_1;
  };

  using _Frame = std::variant<_Enter, _After_m, _After_m_1, _Combine_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified tribonacci_fuel: _Enter -> _After_m -> _After_m_1 -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
              _stack.emplace_back(_After_m{(m + 1), f, ((m + 1) + 1), f});
              _stack.emplace_back(_Enter{m, f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_After_m_1{_result, _f._s2, _f.f_1});
      _stack.emplace_back(_Enter{_f.m, _f.f_0});
    } else if (std::holds_alternative<_After_m_1>(_frame)) {
      auto _f = std::move(std::get<_After_m_1>(_frame));
      _stack.emplace_back(_Combine_m{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (_result + (_f._result_1 + _f._result_0));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::tribonacci(uint64_t n) {
  return tribonacci_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::gcd_fuel(uint64_t fuel, uint64_t a, uint64_t b) {
  uint64_t _loop_b = std::move(b);
  uint64_t _loop_a = std::move(a);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return _loop_a;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_b <= 0) {
        return _loop_a;
      } else {
        uint64_t _x = _loop_b - 1;
        uint64_t _next_b = (_loop_b ? _loop_a % _loop_b : _loop_a);
        uint64_t _next_a = _loop_b;
        _loop_fuel = f;
        _loop_b = _next_b;
        _loop_a = _next_a;
      }
    }
  }
}

uint64_t LoopifyNumbers::gcd(uint64_t a, uint64_t b) {
  return gcd_fuel((a + b), a, b);
}

uint64_t
LoopifyNumbers::binomial(uint64_t n,
                         uint64_t k) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

  struct _Enter {
    uint64_t k;
    uint64_t n;
  };

  /// _After_k_: saves [k_, n_], dispatches next recursive call.
  struct _After_k_ {
    uint64_t k_;
    uint64_t n_;
  };

  /// _Combine_k_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_k_ {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_k_, _Combine_k_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{k, n});
  /// Loopified binomial: _Enter -> _After_k_ -> _Combine_k_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
          _stack.emplace_back(_After_k_{k_, n_});
          _stack.emplace_back(_Enter{k, n_});
        }
      }
    } else if (std::holds_alternative<_After_k_>(_frame)) {
      auto _f = std::move(std::get<_After_k_>(_frame));
      _stack.emplace_back(_Combine_k_{_result});
      _stack.emplace_back(_Enter{_f.k_, _f.n_});
    } else {
      auto _f = std::move(std::get<_Combine_k_>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t
LoopifyNumbers::pascal(uint64_t row,
                       uint64_t col) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

  struct _Enter {
    uint64_t col;
    uint64_t row;
  };

  /// _After_r: saves [c, r], dispatches next recursive call.
  struct _After_r {
    uint64_t c;
    uint64_t r;
  };

  /// _Combine_r: receives partial results, combines with _result from final
  /// call.
  struct _Combine_r {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_r, _Combine_r>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{col, row});
  /// Loopified pascal: _Enter -> _After_r -> _Combine_r.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
          _stack.emplace_back(_After_r{c, r});
          _stack.emplace_back(_Enter{(c + 1), r});
        }
      }
    } else if (std::holds_alternative<_After_r>(_frame)) {
      auto _f = std::move(std::get<_After_r>(_frame));
      _stack.emplace_back(_Combine_r{_result});
      _stack.emplace_back(_Enter{_f.c, _f.r});
    } else {
      auto _f = std::move(std::get<_Combine_r>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::ackermann_fuel(
    uint64_t fuel, uint64_t m,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t m;
    uint64_t fuel;
  };

  /// _Resume_n_: saves [m_, f], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t m_;
    uint64_t f;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, m, fuel});
  /// Loopified ackermann_fuel: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Enter{UINT64_C(1), m_, f});
          } else {
            uint64_t n_ = n - 1;
            _stack.emplace_back(_Resume_n_{m_, f});
            _stack.emplace_back(_Enter{n_, m, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _stack.emplace_back(_Enter{_result, _f.m_, _f.f});
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::ack(uint64_t m, uint64_t n) {
  return ackermann_fuel(UINT64_C(1000), m, n);
}

uint64_t LoopifyNumbers::collatz_length_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  /// _Resume2: resumes after recursive call with _result.
  struct _Resume2 {};

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified collatz_length_fuel: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (n == UINT64_C(1)) {
          _result = UINT64_C(0);
        } else {
          if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
          } else {
            _stack.emplace_back(_Resume2{});
            _stack.emplace_back(_Enter{((UINT64_C(3) * n) + UINT64_C(1)), f});
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_result + 1);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::collatz_length(uint64_t n) {
  return collatz_length_fuel(UINT64_C(1000), n);
}

uint64_t LoopifyNumbers::digitsum_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume__x: saves [_s0], resumes after recursive call with _result.
  struct _Resume__x {
    decltype((UINT64_C(10) ? std::declval<uint64_t &>() % UINT64_C(10)
                           : std::declval<uint64_t &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume__x>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified digitsum_fuel: _Enter -> _Resume__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
          _stack.emplace_back(
              _Resume__x{(UINT64_C(10) ? n % UINT64_C(10) : n)});
          _stack.emplace_back(_Enter{(UINT64_C(10) ? n / UINT64_C(10) : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume__x>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::digitsum(uint64_t n) {
  return digitsum_fuel(UINT64_C(100), n);
}

uint64_t LoopifyNumbers::dec_to_bin_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Cont__x: saves [digit], resumes after recursive call, then processes
  /// rest.
  struct _Cont__x {
    uint64_t digit;
  };

  using _Frame = std::variant<_Enter, _Cont__x>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified dec_to_bin_fuel: _Enter -> _Cont__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
          _stack.emplace_back(_Cont__x{digit});
          _stack.emplace_back(_Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont__x>(_frame));
      uint64_t digit = _f.digit;
      uint64_t rest = _result;
      _result = (digit + (UINT64_C(10) * rest));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::dec_to_bin(uint64_t n) {
  return dec_to_bin_fuel(UINT64_C(100), n);
}

uint64_t
LoopifyNumbers::sum_to(uint64_t n) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_to: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::sum_squares(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_squares: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{(n * n)});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::alternating_sum(bool sign, uint64_t acc, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_acc = std::move(acc);
  bool _loop_sign = std::move(sign);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t new_acc;
      if (_loop_sign) {
        new_acc = (_loop_acc + _loop_n);
      } else {
        new_acc =
            (((_loop_acc - _loop_n) > _loop_acc ? 0 : (_loop_acc - _loop_n)));
      }
      _loop_n = m;
      _loop_acc = new_acc;
      _loop_sign = !(_loop_sign);
    }
  }
}

uint64_t LoopifyNumbers::staircase_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After_m: saves [m, f_0, _s2, f_1], dispatches next recursive call.
  struct _After_m {
    uint64_t m;
    uint64_t f_0;
    uint64_t _s2;
    uint64_t f_1;
  };

  /// _After_m_1: saves [_result, _s1, f], dispatches next recursive call.
  struct _After_m_1 {
    uint64_t _result;
    uint64_t _s1;
    uint64_t f;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result_0;
    uint64_t _result_1;
  };

  using _Frame = std::variant<_Enter, _After_m, _After_m_1, _Combine_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified staircase_fuel: _Enter -> _After_m -> _After_m_1 -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
              _stack.emplace_back(_After_m{(m + 1), f, ((m + 1) + 1), f});
              _stack.emplace_back(_Enter{m, f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_After_m_1{_result, _f._s2, _f.f_1});
      _stack.emplace_back(_Enter{_f.m, _f.f_0});
    } else if (std::holds_alternative<_After_m_1>(_frame)) {
      auto _f = std::move(std::get<_After_m_1>(_frame));
      _stack.emplace_back(_Combine_m{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (_result + (_f._result_1 + _f._result_0));
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
      [](uint64_t x) {
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
uint64_t LoopifyNumbers::sum_while_positive(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_while_positive: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}

/// count_down_by k n counts down from n by steps of k.
/// Tests recursion with non-standard step size.
uint64_t LoopifyNumbers::count_down_by_fuel(
    uint64_t fuel, uint64_t k,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified count_down_by_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{(((n - k) > n ? 0 : (n - k))), f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::count_down_by(uint64_t k, uint64_t n) {
  return count_down_by_fuel(UINT64_C(100), k, n);
}

/// mixed_arith n combines multiplication and addition in recursion.
uint64_t LoopifyNumbers::mixed_arith_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After_m: saves [m, f_0, n_, f_1], dispatches next recursive call.
  struct _After_m {
    uint64_t m;
    uint64_t f_0;
    uint64_t n_;
    uint64_t f_1;
  };

  /// _After_m_1: saves [_result, n_, f], dispatches next recursive call.
  struct _After_m_1 {
    uint64_t _result;
    uint64_t n_;
    uint64_t f;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result_0;
    uint64_t _result_1;
  };

  using _Frame = std::variant<_Enter, _After_m, _After_m_1, _Combine_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified mixed_arith_fuel: _Enter -> _After_m -> _After_m_1 ->
  /// _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
              _stack.emplace_back(_After_m{m, f, n_, f});
              _stack.emplace_back(_Enter{
                  (m == UINT64_C(0)
                       ? UINT64_C(0)
                       : (((m - UINT64_C(1)) > m ? 0 : (m - UINT64_C(1))))),
                  f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_After_m_1{_result, _f.n_, _f.f_1});
      _stack.emplace_back(_Enter{_f.m, _f.f_0});
    } else if (std::holds_alternative<_After_m_1>(_frame)) {
      auto _f = std::move(std::get<_After_m_1>(_frame));
      _stack.emplace_back(_Combine_m{_f._result, _result});
      _stack.emplace_back(_Enter{_f.n_, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = ((_result * _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::mixed_arith(uint64_t n) {
  return mixed_arith_fuel(UINT64_C(1000), n);
}

/// is_even n checks if n is even (mutually recursive with is_odd).
bool LoopifyNumbers::is_even_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return true;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        return true;
      } else {
        uint64_t _inl_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        uint64_t _inl_fuel = f;
        if (_inl_fuel <= 0) {
          return false;
        } else {
          uint64_t f = _inl_fuel - 1;
          if (_inl_n == UINT64_C(0)) {
            return false;
          } else {
            _loop_n = ((
                (_inl_n - UINT64_C(1)) > _inl_n ? 0 : (_inl_n - UINT64_C(1))));
            _loop_fuel = f;
          }
        }
      }
    }
  }
}

bool LoopifyNumbers::is_odd_fuel(uint64_t fuel, uint64_t n) {
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      return false;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(0)) {
        return false;
      } else {
        uint64_t _inl_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        uint64_t _inl_fuel = f;
        if (_inl_fuel <= 0) {
          return true;
        } else {
          uint64_t f = _inl_fuel - 1;
          if (_inl_n == UINT64_C(0)) {
            return true;
          } else {
            _loop_n = ((
                (_inl_n - UINT64_C(1)) > _inl_n ? 0 : (_inl_n - UINT64_C(1))));
            _loop_fuel = f;
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
} /// power b e computes b^e.

uint64_t
LoopifyNumbers::power(uint64_t b,
                      uint64_t e) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

  struct _Enter {
    uint64_t e;
  };

  /// _Resume_e_: saves [b], resumes after recursive call with _result.
  struct _Resume_e_ {
    uint64_t b;
  };

  using _Frame = std::variant<_Enter, _Resume_e_>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{e});
  /// Loopified power: _Enter -> _Resume_e_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t e = _f.e;
      if (e <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t e_ = e - 1;
        _stack.emplace_back(_Resume_e_{b});
        _stack.emplace_back(_Enter{e_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_e_>(_frame));
      _result = (_f.b * _result);
    }
  }
  return _result;
}

/// power_mod b e m computes (b^e) mod m efficiently.
uint64_t LoopifyNumbers::power_mod_fuel(
    uint64_t fuel, uint64_t b, uint64_t e,
    uint64_t
        m) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t e;
    uint64_t fuel;
  };

  /// _Cont1: saves [m], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t m;
  };

  /// _Cont2: saves [b, m], resumes after recursive call, then processes rest.
  struct _Cont2 {
    uint64_t b;
    uint64_t m;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{e, fuel});
  /// Loopified power_mod_fuel: _Enter -> _Cont1 -> _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Cont1{m});
            _stack.emplace_back(_Enter{(UINT64_C(2) ? e / UINT64_C(2) : 0), f});
          } else {
            _stack.emplace_back(_Cont2{b, m});
            _stack.emplace_back(_Enter{(UINT64_C(2) ? e / UINT64_C(2) : 0), f});
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t m = _f.m;
      uint64_t half = _result;
      _result = (m ? (half * half) % m : (half * half));
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t b = _f.b;
      uint64_t m = _f.m;
      uint64_t half = _result;
      _result = (m ? (b * (half * half)) % m : (b * (half * half)));
    }
  }
  return _result;
}

uint64_t LoopifyNumbers::power_mod(uint64_t b, uint64_t e, uint64_t m) {
  return power_mod_fuel(UINT64_C(1000), b, e, m);
}

/// sum_divisors n sums all divisors of n (excluding n itself).
uint64_t LoopifyNumbers::sum_divisors_aux(
    uint64_t n,
    uint64_t
        k) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t k;
  };

  /// _Resume1: saves [k], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t k;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{k});
  /// Loopified sum_divisors_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Resume1{k});
            _stack.emplace_back(_Enter{k_});
          } else {
            _stack.emplace_back(_Enter{k_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.k + _result);
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
      return sum_divisors_aux(
          n_, (((n_ - UINT64_C(1)) > n_ ? 0 : (n_ - UINT64_C(1)))));
    }
  }
}

/// sum_odd_indices l and sum_even_indices l are mutually recursive.
/// sum_odd_indices adds elements at odd positions (0, 2, 4...).
/// sum_even_indices processes even positions (1, 3, 5...) by calling
/// sum_odd_indices.
uint64_t LoopifyNumbers::sum_odd_indices_fuel(uint64_t fuel,
                                              const List<uint64_t> &l) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return (a0 + sum_even_indices_fuel(f, *a1));
    }
  }
}

uint64_t LoopifyNumbers::sum_even_indices_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified sum_even_indices_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          const List<uint64_t> &_inl_l = *a1;
          uint64_t _inl_fuel = f;
          if (_inl_fuel <= 0) {
            _result = UINT64_C(0);
          } else {
            uint64_t f = _inl_fuel - 1;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _inl_l.v())) {
              _result = UINT64_C(0);
            } else {
              const auto &[a0, a1] =
                  std::get<typename List<uint64_t>::Cons>(_inl_l.v());
              _stack.emplace_back(_Resume_Cons{a0});
              _stack.emplace_back(_Enter{a1.get(), f});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + _result);
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
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t f = _loop_fuel - 1;
      if (_loop_n == UINT64_C(1)) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()));
        break;
      } else {
        if ((UINT64_C(2) ? _loop_n % UINT64_C(2) : _loop_n) == UINT64_C(0)) {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(_loop_n, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_n = (UINT64_C(2) ? _loop_n / UINT64_C(2) : 0);
          _loop_fuel = f;
          continue;
        } else {
          if ((UINT64_C(3) ? _loop_n % UINT64_C(3) : _loop_n) == UINT64_C(0)) {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(_loop_n, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_n = (UINT64_C(3) ? _loop_n / UINT64_C(3) : 0);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = std::make_unique<List<uint64_t>>(
                typename List<uint64_t>::Cons(_loop_n, nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_n = ((UINT64_C(3) * _loop_n) + UINT64_C(1));
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyNumbers::collatz_list(uint64_t n) {
  return collatz_list_fuel(UINT64_C(1000), n);
}

/// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
uint64_t LoopifyNumbers::sum_divisible_by(
    uint64_t k,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume1: saves [n], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_divisible_by: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        if ((k ? n % k : n) == UINT64_C(0)) {
          _stack.emplace_back(_Resume1{n});
          _stack.emplace_back(_Enter{m});
        } else {
          _stack.emplace_back(_Enter{m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}
