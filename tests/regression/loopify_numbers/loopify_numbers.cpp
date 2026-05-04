#include <loopify_numbers.h>

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
unsigned int LoopifyNumbers::factorial(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified factorial: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 1u;
      } else {
        unsigned int m = n - 1;
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

unsigned int LoopifyNumbers::fib(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _After_m: saves [n_], dispatches next recursive call.
  struct _After_m {
    unsigned int n_;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After_m, _Combine_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified fib: _Enter -> _After_m -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int m = n_ - 1;
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
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::tribonacci_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After_m: saves [m, f_0, _s2, f_1], dispatches next recursive call.
  struct _After_m {
    unsigned int m;
    unsigned int f_0;
    unsigned int _s2;
    unsigned int f_1;
  };

  /// _After_m_1: saves [_result, _s1, f], dispatches next recursive call.
  struct _After_m_1 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int f;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After_m, _After_m_1, _Combine_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified tribonacci_fuel: _Enter -> _After_m -> _After_m_1 -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 0u;
        } else {
          unsigned int n0 = n - 1;
          if (n0 <= 0) {
            _result = 0u;
          } else {
            unsigned int n1 = n0 - 1;
            if (n1 <= 0) {
              _result = 1u;
            } else {
              unsigned int m = n1 - 1;
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

unsigned int LoopifyNumbers::tribonacci(const unsigned int n) {
  return tribonacci_fuel(100u, n);
}

unsigned int LoopifyNumbers::gcd_fuel(const unsigned int fuel,
                                      const unsigned int a,
                                      const unsigned int b) {
  unsigned int _result;
  unsigned int _loop_b = b;
  unsigned int _loop_a = a;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = _loop_a;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_b <= 0) {
        _result = _loop_a;
        break;
      } else {
        unsigned int _x = _loop_b - 1;
        unsigned int _next_b = (_loop_b ? _loop_a % _loop_b : _loop_a);
        unsigned int _next_a = _loop_b;
        _loop_fuel = f;
        _loop_b = _next_b;
        _loop_a = _next_a;
      }
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::gcd(const unsigned int a, const unsigned int b) {
  return gcd_fuel((a + b), a, b);
}

unsigned int LoopifyNumbers::binomial(
    const unsigned int n,
    const unsigned int
        k) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int k;
    unsigned int n;
  };

  /// _After_k_: saves [k_, n_], dispatches next recursive call.
  struct _After_k_ {
    unsigned int k_;
    unsigned int n_;
  };

  /// _Combine_k_: receives partial results, combines with _result from final
  /// call.
  struct _Combine_k_ {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After_k_, _Combine_k_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{k, n});
  /// Loopified binomial: _Enter -> _After_k_ -> _Combine_k_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int k = _f.k;
      const unsigned int n = _f.n;
      if (n <= 0) {
        if (k <= 0) {
          _result = 1u;
        } else {
          unsigned int _x = k - 1;
          _result = 0u;
        }
      } else {
        unsigned int n_ = n - 1;
        if (k <= 0) {
          _result = 1u;
        } else {
          unsigned int k_ = k - 1;
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
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::pascal(
    const unsigned int row,
    const unsigned int
        col) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int col;
    unsigned int row;
  };

  /// _After_r: saves [c, r], dispatches next recursive call.
  struct _After_r {
    unsigned int c;
    unsigned int r;
  };

  /// _Combine_r: receives partial results, combines with _result from final
  /// call.
  struct _Combine_r {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After_r, _Combine_r>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{col, row});
  /// Loopified pascal: _Enter -> _After_r -> _Combine_r.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int col = _f.col;
      const unsigned int row = _f.row;
      if (col <= 0) {
        _result = 1u;
      } else {
        unsigned int c = col - 1;
        if (row <= 0) {
          _result = 0u;
        } else {
          unsigned int r = row - 1;
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
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::ackermann_fuel(
    const unsigned int fuel, const unsigned int m,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int m;
    unsigned int fuel;
  };

  /// _Resume_n_: saves [m_, f], resumes after recursive call with _result.
  struct _Resume_n_ {
    unsigned int m_;
    unsigned int f;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, m, fuel});
  /// Loopified ackermann_fuel: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int m = _f.m;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (m <= 0) {
          _result = (n + 1);
        } else {
          unsigned int m_ = m - 1;
          if (n <= 0) {
            _stack.emplace_back(_Enter{1u, m_, f});
          } else {
            unsigned int n_ = n - 1;
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

unsigned int LoopifyNumbers::ack(const unsigned int m, const unsigned int n) {
  return ackermann_fuel(1000u, m, n);
}

unsigned int LoopifyNumbers::collatz_length_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  /// _Resume2: resumes after recursive call with _result.
  struct _Resume2 {};

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified collatz_length_fuel: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n == 1u) {
          _result = 0u;
        } else {
          if ((2u ? n % 2u : n) == 0u) {
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{(2u ? n / 2u : 0), f});
          } else {
            _stack.emplace_back(_Resume2{});
            _stack.emplace_back(_Enter{((3u * n) + 1u), f});
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

unsigned int LoopifyNumbers::collatz_length(const unsigned int n) {
  return collatz_length_fuel(1000u, n);
}

unsigned int LoopifyNumbers::digitsum_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume__x: saves [_s0], resumes after recursive call with _result.
  struct _Resume__x {
    decltype((10u ? std::declval<const unsigned int &>() % 10u
                  : std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume__x>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified digitsum_fuel: _Enter -> _Resume__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 0u;
        } else {
          unsigned int _x = n - 1;
          _stack.emplace_back(_Resume__x{(10u ? n % 10u : n)});
          _stack.emplace_back(_Enter{(10u ? n / 10u : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume__x>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::digitsum(const unsigned int n) {
  return digitsum_fuel(100u, n);
}

unsigned int LoopifyNumbers::dec_to_bin_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Cont__x: saves [digit], resumes after recursive call, then processes
  /// rest.
  struct _Cont__x {
    unsigned int digit;
  };

  using _Frame = std::variant<_Enter, _Cont__x>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified dec_to_bin_fuel: _Enter -> _Cont__x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 0u;
        } else {
          unsigned int _x = n - 1;
          unsigned int digit = (2u ? n % 2u : n);
          _stack.emplace_back(_Cont__x{digit});
          _stack.emplace_back(_Enter{(2u ? n / 2u : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont__x>(_frame));
      unsigned int digit = _f.digit;
      unsigned int rest = _result;
      _result = (digit + (10u * rest));
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::dec_to_bin(const unsigned int n) {
  return dec_to_bin_fuel(100u, n);
}

unsigned int LoopifyNumbers::sum_to(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_to: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
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

unsigned int LoopifyNumbers::sum_squares(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_squares: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
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

unsigned int LoopifyNumbers::alternating_sum(const bool sign,
                                             const unsigned int acc,
                                             const unsigned int n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_acc = acc;
  bool _loop_sign = sign;
  while (true) {
    if (_loop_n <= 0) {
      _result = _loop_acc;
      break;
    } else {
      unsigned int m = _loop_n - 1;
      unsigned int new_acc;
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
  return _result;
}

unsigned int LoopifyNumbers::staircase_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After_m: saves [m, f_0, _s2, f_1], dispatches next recursive call.
  struct _After_m {
    unsigned int m;
    unsigned int f_0;
    unsigned int _s2;
    unsigned int f_1;
  };

  /// _After_m_1: saves [_result, _s1, f], dispatches next recursive call.
  struct _After_m_1 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int f;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After_m, _After_m_1, _Combine_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified staircase_fuel: _Enter -> _After_m -> _After_m_1 -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 1u;
        } else {
          unsigned int n0 = n - 1;
          if (n0 <= 0) {
            _result = 1u;
          } else {
            unsigned int n1 = n0 - 1;
            if (n1 <= 0) {
              _result = 2u;
            } else {
              unsigned int m = n1 - 1;
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

unsigned int LoopifyNumbers::staircase(const unsigned int n) {
  return staircase_fuel(100u, n);
}

/// iterate_pred n applies predecessor n times, starting from n.
/// Tests church-style iteration with concrete function.
unsigned int LoopifyNumbers::iterate_pred(const unsigned int n) {
  return church(
      n,
      [](const unsigned int x) {
        if (x <= 0) {
          return 0u;
        } else {
          unsigned int m = x - 1;
          return m;
        }
      },
      n);
}

/// sum_while_positive n sums numbers from n down to 0, but only positive ones.
/// Tests conditional accumulation in recursion.
unsigned int LoopifyNumbers::sum_while_positive(
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_while_positive: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
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
unsigned int LoopifyNumbers::count_down_by_fuel(
    const unsigned int fuel, const unsigned int k,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: resumes after recursive call with _result.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified count_down_by_fuel: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 1u;
        } else {
          unsigned int _x = n - 1;
          if (n < k) {
            _result = 1u;
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

unsigned int LoopifyNumbers::count_down_by(const unsigned int k,
                                           const unsigned int n) {
  return count_down_by_fuel(100u, k, n);
}

/// mixed_arith n combines multiplication and addition in recursion.
unsigned int LoopifyNumbers::mixed_arith_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After_m: saves [m, f_0, n_, f_1], dispatches next recursive call.
  struct _After_m {
    unsigned int m;
    unsigned int f_0;
    unsigned int n_;
    unsigned int f_1;
  };

  /// _After_m_1: saves [_result, n_, f], dispatches next recursive call.
  struct _After_m_1 {
    unsigned int _result;
    unsigned int n_;
    unsigned int f;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After_m, _After_m_1, _Combine_m>;
  unsigned int _result{};
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
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 1u;
        } else {
          unsigned int n0 = n - 1;
          if (n0 <= 0) {
            _result = 1u;
          } else {
            unsigned int n_ = n0 - 1;
            if (n_ <= 0) {
              _result = 1u;
            } else {
              unsigned int m = n_ - 1;
              _stack.emplace_back(_After_m{m, f, n_, f});
              _stack.emplace_back(
                  _Enter{(m == 0u ? 0u : (((m - 1u) > m ? 0 : (m - 1u)))), f});
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

unsigned int LoopifyNumbers::mixed_arith(const unsigned int n) {
  return mixed_arith_fuel(1000u, n);
}

/// is_even n checks if n is even (mutually recursive with is_odd).
bool LoopifyNumbers::is_even_fuel(const unsigned int fuel,
                                  const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = true;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        _result = true;
        break;
      } else {
        const unsigned int _inl_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        const unsigned int _inl_fuel = f;
        if (_inl_fuel <= 0) {
          _result = false;
          break;
        } else {
          unsigned int f = _inl_fuel - 1;
          if (_inl_n == 0u) {
            _result = false;
            break;
          } else {
            _loop_n = (((_inl_n - 1u) > _inl_n ? 0 : (_inl_n - 1u)));
            _loop_fuel = f;
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifyNumbers::is_odd_fuel(const unsigned int fuel,
                                 const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = false;
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        _result = false;
        break;
      } else {
        const unsigned int _inl_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        const unsigned int _inl_fuel = f;
        if (_inl_fuel <= 0) {
          _result = true;
          break;
        } else {
          unsigned int f = _inl_fuel - 1;
          if (_inl_n == 0u) {
            _result = true;
            break;
          } else {
            _loop_n = (((_inl_n - 1u) > _inl_n ? 0 : (_inl_n - 1u)));
            _loop_fuel = f;
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifyNumbers::is_even(const unsigned int n) {
  return is_even_fuel(1000u, n);
}

bool LoopifyNumbers::is_odd(const unsigned int n) {
  return is_odd_fuel(1000u, n);
}

/// power b e computes b^e.
unsigned int LoopifyNumbers::power(
    const unsigned int b,
    const unsigned int
        e) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int e;
  };

  /// _Resume_e_: saves [b], resumes after recursive call with _result.
  struct _Resume_e_ {
    unsigned int b;
  };

  using _Frame = std::variant<_Enter, _Resume_e_>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{e});
  /// Loopified power: _Enter -> _Resume_e_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int e = _f.e;
      if (e <= 0) {
        _result = 1u;
      } else {
        unsigned int e_ = e - 1;
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
unsigned int LoopifyNumbers::power_mod_fuel(
    const unsigned int fuel, const unsigned int b, const unsigned int e,
    const unsigned int
        m) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int e;
    unsigned int fuel;
  };

  /// _Cont1: saves [m], resumes after recursive call, then processes rest.
  struct _Cont1 {
    unsigned int m;
  };

  /// _Cont2: saves [b, m], resumes after recursive call, then processes rest.
  struct _Cont2 {
    unsigned int b;
    unsigned int m;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{e, fuel});
  /// Loopified power_mod_fuel: _Enter -> _Cont1 -> _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int e = _f.e;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (e == 0u) {
          _result = 1u;
        } else {
          if ((2u ? e % 2u : e) == 0u) {
            _stack.emplace_back(_Cont1{m});
            _stack.emplace_back(_Enter{(2u ? e / 2u : 0), f});
          } else {
            _stack.emplace_back(_Cont2{b, m});
            _stack.emplace_back(_Enter{(2u ? e / 2u : 0), f});
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      const unsigned int m = _f.m;
      unsigned int half = _result;
      _result = (m ? (half * half) % m : (half * half));
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      const unsigned int b = _f.b;
      const unsigned int m = _f.m;
      unsigned int half = _result;
      _result = (m ? (b * (half * half)) % m : (b * (half * half)));
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::power_mod(const unsigned int b,
                                       const unsigned int e,
                                       const unsigned int m) {
  return power_mod_fuel(1000u, b, e, m);
}

/// sum_divisors n sums all divisors of n (excluding n itself).
unsigned int LoopifyNumbers::sum_divisors_aux(
    const unsigned int n,
    const unsigned int
        k) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int k;
  };

  /// _Resume1: saves [k], resumes after recursive call with _result.
  struct _Resume1 {
    unsigned int k;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{k});
  /// Loopified sum_divisors_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int k = _f.k;
      if (k <= 0) {
        _result = 0u;
      } else {
        unsigned int k_ = k - 1;
        if (k_ <= 0) {
          _result = 0u;
        } else {
          unsigned int _x = k_ - 1;
          if ((k ? n % k : n) == 0u) {
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

unsigned int LoopifyNumbers::sum_divisors(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    if (n_ <= 0) {
      return 0u;
    } else {
      unsigned int _x = n_ - 1;
      return sum_divisors_aux(n_, (((n_ - 1u) > n_ ? 0 : (n_ - 1u))));
    }
  }
}

/// sum_odd_indices l and sum_even_indices l are mutually recursive.
/// sum_odd_indices adds elements at odd positions (0, 2, 4...).
/// sum_even_indices processes even positions (1, 3, 5...) by calling
/// sum_odd_indices.
unsigned int LoopifyNumbers::sum_odd_indices_fuel(const unsigned int fuel,
                                                  const List<unsigned int> &l) {
  if (fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = fuel - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      return (d_a0 + sum_even_indices_fuel(f, *(d_a1)));
    }
  }
}

unsigned int LoopifyNumbers::sum_even_indices_fuel(
    const unsigned int fuel,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
    unsigned int fuel;
  };

  /// _Resume_Cons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified sum_even_indices_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          const List<unsigned int> &_inl_l = *(d_a1);
          const unsigned int _inl_fuel = f;
          if (_inl_fuel <= 0) {
            _result = 0u;
          } else {
            unsigned int f = _inl_fuel - 1;
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    _inl_l.v())) {
              _result = 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<unsigned int>::Cons>(_inl_l.v());
              _stack.emplace_back(_Resume_Cons{d_a0});
              _stack.emplace_back(_Enter{d_a1.get(), f});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::sum_odd_indices(const List<unsigned int> &l) {
  return sum_odd_indices_fuel(l.length(), l);
}

unsigned int LoopifyNumbers::sum_even_indices(const List<unsigned int> &l) {
  return sum_even_indices_fuel(l.length(), l);
}

/// collatz_list n generates collatz sequence as a list.
List<unsigned int> LoopifyNumbers::collatz_list_fuel(const unsigned int fuel,
                                                     const unsigned int n) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 1u) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(1u, List<unsigned int>::nil()));
        break;
      } else {
        if ((2u ? _loop_n % 2u : _loop_n) == 0u) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(_loop_n, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_n = (2u ? _loop_n / 2u : 0);
          _loop_fuel = f;
          continue;
        } else {
          if ((3u ? _loop_n % 3u : _loop_n) == 0u) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(_loop_n, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            _loop_n = (3u ? _loop_n / 3u : 0);
            _loop_fuel = f;
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(_loop_n, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            _loop_n = ((3u * _loop_n) + 1u);
            _loop_fuel = f;
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyNumbers::collatz_list(const unsigned int n) {
  return collatz_list_fuel(1000u, n);
}

/// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
unsigned int LoopifyNumbers::sum_divisible_by(
    const unsigned int k,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
  };

  /// _Resume1: saves [n], resumes after recursive call with _result.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_divisible_by: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        if ((k ? n % k : n) == 0u) {
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
