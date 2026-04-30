#include <loopify_numbers.h>

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
unsigned int LoopifyNumbers::factorial(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 1u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Resume1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n * _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::fib(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Intermediate: saves [n_], dispatches next recursive call.
  struct _After2 {
    unsigned int n_;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int n_ = n - 1;
        if (n_ <= 0) {
          _result = 1u;
        } else {
          unsigned int m = n_ - 1;
          _stack.emplace_back(_After2{n_});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f.n_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::tribonacci_fuel(const unsigned int &fuel,
                                             const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Intermediate: saves [_s0, f_0, _s2, f_1], dispatches next recursive call.
  struct _After1 {
    unsigned int _s0;
    unsigned int f_0;
    unsigned int _s2;
    unsigned int f_1;
  };

  /// Intermediate: saves [_result, _s1, f], dispatches next recursive call.
  struct _After2 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int f;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine3 {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _After1, _After2, _Combine3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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
              _stack.emplace_back(_After1{(m + 1), f, ((m + 1) + 1), f});
              _stack.emplace_back(_Enter{m, f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After1>(_frame)) {
      auto _f = std::move(std::get<_After1>(_frame));
      _stack.emplace_back(_After2{_result, _f._s2, _f.f_1});
      _stack.emplace_back(_Enter{_f._s0, _f.f_0});
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine3{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = (_result + (_f._result_1 + _f._result_0));
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::tribonacci(const unsigned int &n) {
  return tribonacci_fuel(100u, n);
}

unsigned int LoopifyNumbers::gcd_fuel(const unsigned int &fuel, unsigned int a,
                                      const unsigned int &b) {
  unsigned int _result;
  unsigned int _loop_b = b;
  unsigned int _loop_a = std::move(a);
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
        unsigned int _next_fuel = f;
        _loop_b = std::move(_next_b);
        _loop_a = std::move(_next_a);
        _loop_fuel = std::move(_next_fuel);
      }
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::gcd(const unsigned int &a, const unsigned int &b) {
  return gcd_fuel((a + b), a, b);
}

unsigned int LoopifyNumbers::binomial(const unsigned int &n,
                                      const unsigned int &k) {
  struct _Enter {
    unsigned int k;
    unsigned int n;
  };

  /// Intermediate: saves [k_, n_], dispatches next recursive call.
  struct _After2 {
    unsigned int k_;
    unsigned int n_;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{k, n});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &k = _f.k;
      const unsigned int &n = _f.n;
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
          _stack.emplace_back(_After2{k_, n_});
          _stack.emplace_back(_Enter{k, n_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f.k_, _f.n_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::pascal(const unsigned int &row,
                                    const unsigned int &col) {
  struct _Enter {
    unsigned int col;
    unsigned int row;
  };

  /// Intermediate: saves [c, r], dispatches next recursive call.
  struct _After2 {
    unsigned int c;
    unsigned int r;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{col, row});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &col = _f.col;
      const unsigned int &row = _f.row;
      if (col <= 0) {
        _result = 1u;
      } else {
        unsigned int c = col - 1;
        if (row <= 0) {
          _result = 0u;
        } else {
          unsigned int r = row - 1;
          _stack.emplace_back(_After2{c, r});
          _stack.emplace_back(_Enter{(c + 1), r});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f.c, _f.r});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::ackermann_fuel(const unsigned int &fuel,
                                            const unsigned int &m,
                                            unsigned int n) {
  struct _Enter {
    unsigned int n;
    unsigned int m;
    unsigned int fuel;
  };

  /// Continuation: saves [m_, f] across recursive call.
  struct _Resume1 {
    unsigned int m_;
    unsigned int f;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, m, fuel});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      unsigned int n = std::move(_f.n);
      const unsigned int &m = _f.m;
      const unsigned int &fuel = _f.fuel;
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
            _stack.emplace_back(_Resume1{m_, f});
            _stack.emplace_back(_Enter{n_, m, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _stack.emplace_back(_Enter{_result, _f.m_, _f.f});
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::ack(const unsigned int &m, const unsigned int &n) {
  return ackermann_fuel(1000u, m, n);
}

unsigned int LoopifyNumbers::collatz_length_fuel(const unsigned int &fuel,
                                                 const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Continuation: saves across recursive call.
  struct _Resume1 {};

  /// Continuation: saves across recursive call.
  struct _Resume2 {};

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _Resume1, _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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

unsigned int LoopifyNumbers::collatz_length(const unsigned int &n) {
  return collatz_length_fuel(1000u, n);
}

unsigned int LoopifyNumbers::digitsum_fuel(const unsigned int &fuel,
                                           const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype((10u ? std::declval<const unsigned int &>() % 10u
                  : std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 0u;
        } else {
          unsigned int _x = n - 1;
          _stack.emplace_back(_Resume1{(10u ? n % 10u : n)});
          _stack.emplace_back(_Enter{(10u ? n / 10u : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::digitsum(const unsigned int &n) {
  return digitsum_fuel(100u, n);
}

unsigned int LoopifyNumbers::dec_to_bin_fuel(const unsigned int &fuel,
                                             const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Continuation: saves [digit] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int digit;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 0u;
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = 0u;
        } else {
          unsigned int _x = n - 1;
          unsigned int digit = (2u ? n % 2u : n);
          _stack.emplace_back(_Cont1{digit});
          _stack.emplace_back(_Enter{(2u ? n / 2u : 0), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int digit = std::move(_f.digit);
      unsigned int rest = _result;
      _result = (digit + (10u * rest));
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::dec_to_bin(const unsigned int &n) {
  return dec_to_bin_fuel(100u, n);
}

unsigned int LoopifyNumbers::sum_to(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Resume1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::sum_squares(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype((std::declval<const unsigned int &>() *
              std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Resume1{(n * n)});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::alternating_sum(const bool &sign, unsigned int acc,
                                             const unsigned int &n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_acc = std::move(acc);
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
      unsigned int _next_n = m;
      unsigned int _next_acc = new_acc;
      bool _next_sign = !(_loop_sign);
      _loop_n = std::move(_next_n);
      _loop_acc = std::move(_next_acc);
      _loop_sign = std::move(_next_sign);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::staircase_fuel(const unsigned int &fuel,
                                            const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Intermediate: saves [_s0, f_0, _s2, f_1], dispatches next recursive call.
  struct _After1 {
    unsigned int _s0;
    unsigned int f_0;
    unsigned int _s2;
    unsigned int f_1;
  };

  /// Intermediate: saves [_result, _s1, f], dispatches next recursive call.
  struct _After2 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int f;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine3 {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _After1, _After2, _Combine3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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
              _stack.emplace_back(_After1{(m + 1), f, ((m + 1) + 1), f});
              _stack.emplace_back(_Enter{m, f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After1>(_frame)) {
      auto _f = std::move(std::get<_After1>(_frame));
      _stack.emplace_back(_After2{_result, _f._s2, _f.f_1});
      _stack.emplace_back(_Enter{_f._s0, _f.f_0});
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine3{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = (_result + (_f._result_1 + _f._result_0));
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::staircase(const unsigned int &n) {
  return staircase_fuel(100u, n);
}

/// iterate_pred n applies predecessor n times, starting from n.
/// Tests church-style iteration with concrete function.
unsigned int LoopifyNumbers::iterate_pred(const unsigned int &n) {
  return church(
      n,
      [](const unsigned int &x) {
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
unsigned int LoopifyNumbers::sum_while_positive(const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Resume1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}

/// count_down_by k n counts down from n by steps of k.
/// Tests recursion with non-standard step size.
unsigned int LoopifyNumbers::count_down_by_fuel(const unsigned int &fuel,
                                                const unsigned int &k,
                                                const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Continuation: saves across recursive call.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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

unsigned int LoopifyNumbers::count_down_by(const unsigned int &k,
                                           const unsigned int &n) {
  return count_down_by_fuel(100u, k, n);
}

/// mixed_arith n combines multiplication and addition in recursion.
unsigned int LoopifyNumbers::mixed_arith_fuel(const unsigned int &fuel,
                                              const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// Intermediate: saves [m, f_0, n_, f_1], dispatches next recursive call.
  struct _After1 {
    unsigned int m;
    unsigned int f_0;
    unsigned int n_;
    unsigned int f_1;
  };

  /// Intermediate: saves [_result, n_, f], dispatches next recursive call.
  struct _After2 {
    unsigned int _result;
    unsigned int n_;
    unsigned int f;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine3 {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Frame dispatch: _Enter, _After1, _After2, _Combine3.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
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
              _stack.emplace_back(_After1{m, f, n_, f});
              _stack.emplace_back(
                  _Enter{(m == 0u ? 0u : (((m - 1u) > m ? 0 : (m - 1u)))), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After1>(_frame)) {
      auto _f = std::move(std::get<_After1>(_frame));
      _stack.emplace_back(_After2{_result, _f.n_, _f.f_1});
      _stack.emplace_back(_Enter{_f.m, _f.f_0});
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine3{_f._result, _result});
      _stack.emplace_back(_Enter{_f.n_, _f.f});
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = ((_result * _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::mixed_arith(const unsigned int &n) {
  return mixed_arith_fuel(1000u, n);
}

/// is_even n checks if n is even (mutually recursive with is_odd).
bool LoopifyNumbers::is_even_fuel(const unsigned int &fuel,
                                  const unsigned int &n) {
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
        const unsigned int &_inl_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        const unsigned int &_inl_fuel = f;
        if (_inl_fuel <= 0) {
          _result = false;
          break;
        } else {
          unsigned int f = _inl_fuel - 1;
          if (_inl_n == 0u) {
            _result = false;
            break;
          } else {
            unsigned int _next_n =
                (((_inl_n - 1u) > _inl_n ? 0 : (_inl_n - 1u)));
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifyNumbers::is_odd_fuel(const unsigned int &fuel,
                                 const unsigned int &n) {
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
        const unsigned int &_inl_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        const unsigned int &_inl_fuel = f;
        if (_inl_fuel <= 0) {
          _result = true;
          break;
        } else {
          unsigned int f = _inl_fuel - 1;
          if (_inl_n == 0u) {
            _result = true;
            break;
          } else {
            unsigned int _next_n =
                (((_inl_n - 1u) > _inl_n ? 0 : (_inl_n - 1u)));
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
          }
        }
      }
    }
  }
  return _result;
}

bool LoopifyNumbers::is_even(const unsigned int &n) {
  return is_even_fuel(1000u, n);
}

bool LoopifyNumbers::is_odd(const unsigned int &n) {
  return is_odd_fuel(1000u, n);
}

/// power b e computes b^e.
unsigned int LoopifyNumbers::power(const unsigned int &b,
                                   const unsigned int &e) {
  struct _Enter {
    unsigned int e;
  };

  /// Continuation: saves [b] across recursive call.
  struct _Resume1 {
    unsigned int b;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{e});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &e = _f.e;
      if (e <= 0) {
        _result = 1u;
      } else {
        unsigned int e_ = e - 1;
        _stack.emplace_back(_Resume1{b});
        _stack.emplace_back(_Enter{e_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.b * _result);
    }
  }
  return _result;
}

/// power_mod b e m computes (b^e) mod m efficiently.
unsigned int LoopifyNumbers::power_mod_fuel(const unsigned int &fuel,
                                            const unsigned int &b,
                                            const unsigned int &e,
                                            const unsigned int &m) {
  struct _Enter {
    unsigned int e;
    unsigned int fuel;
  };

  /// Continuation: saves [m] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int m;
  };

  /// Continuation: saves [b, m] across recursive call, then processes rest.
  struct _Cont2 {
    unsigned int b;
    unsigned int m;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{e, fuel});
  /// Frame dispatch: _Enter, _Cont1, _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &e = _f.e;
      const unsigned int &fuel = _f.fuel;
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
      const unsigned int &m = _f.m;
      unsigned int half = _result;
      _result = (m ? (half * half) % m : (half * half));
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      const unsigned int &b = _f.b;
      const unsigned int &m = _f.m;
      unsigned int half = _result;
      _result = (m ? (b * (half * half)) % m : (b * (half * half)));
    }
  }
  return _result;
}

unsigned int LoopifyNumbers::power_mod(const unsigned int &b,
                                       const unsigned int &e,
                                       const unsigned int &m) {
  return power_mod_fuel(1000u, b, e, m);
}

/// sum_divisors n sums all divisors of n (excluding n itself).
unsigned int LoopifyNumbers::sum_divisors_aux(const unsigned int &n,
                                              const unsigned int &k) {
  struct _Enter {
    unsigned int k;
  };

  /// Continuation: saves [k] across recursive call.
  struct _Resume1 {
    unsigned int k;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{k});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &k = _f.k;
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

unsigned int LoopifyNumbers::sum_divisors(const unsigned int &n) {
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
unsigned int LoopifyNumbers::sum_odd_indices_fuel(const unsigned int &fuel,
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

unsigned int
LoopifyNumbers::sum_even_indices_fuel(const unsigned int &fuel,
                                      const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
    unsigned int fuel;
  };

  /// Continuation: saves [d_a0] across recursive call.
  struct _Resume1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      const unsigned int &fuel = _f.fuel;
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
          const unsigned int &_inl_fuel = f;
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
              _stack.emplace_back(_Resume1{d_a0});
              _stack.emplace_back(_Enter{d_a1.get(), f});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
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
List<unsigned int> LoopifyNumbers::collatz_list_fuel(const unsigned int &fuel,
                                                     unsigned int n) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = std::move(n);
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
          unsigned int _next_n = (2u ? _loop_n / 2u : 0);
          unsigned int _next_fuel = f;
          _loop_n = std::move(_next_n);
          _loop_fuel = std::move(_next_fuel);
          continue;
        } else {
          if ((3u ? _loop_n % 3u : _loop_n) == 0u) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(_loop_n, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            unsigned int _next_n = (3u ? _loop_n / 3u : 0);
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(_loop_n, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            unsigned int _next_n = ((3u * _loop_n) + 1u);
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyNumbers::collatz_list(const unsigned int &n) {
  return collatz_list_fuel(1000u, n);
}

/// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
unsigned int LoopifyNumbers::sum_divisible_by(const unsigned int &k,
                                              const unsigned int &n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
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
