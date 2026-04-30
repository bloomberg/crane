#include <loopify_classics.h>

unsigned int LoopifyClassics::factorial(const unsigned int &n) {
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
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Resume1{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n * _result);
    }
  }
  return _result;
}

unsigned int LoopifyClassics::fib(const unsigned int &n) {
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
          unsigned int n__ = n_ - 1;
          _stack.emplace_back(_After2{n_});
          _stack.emplace_back(_Enter{n__});
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

unsigned int LoopifyClassics::ack_fuel(const unsigned int &fuel,
                                       const unsigned int &m,
                                       const unsigned int &n) {
  struct _Enter {
    unsigned int n;
    unsigned int m;
    unsigned int fuel;
  };

  /// Continuation: saves [fuel_, m] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int fuel_;
    unsigned int m;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, m, fuel});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &m = _f.m;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = (n + 1u);
      } else {
        unsigned int fuel_ = fuel - 1;
        if (m == 0u) {
          _result = (n + 1u);
        } else {
          if (n == 0u) {
            _stack.emplace_back(
                _Enter{1u, (((m - 1u) > m ? 0 : (m - 1u))), fuel_});
          } else {
            _stack.emplace_back(_Cont1{fuel_, m});
            _stack.emplace_back(
                _Enter{(((n - 1u) > n ? 0 : (n - 1u))), m, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int fuel_ = std::move(_f.fuel_);
      const unsigned int &m = _f.m;
      unsigned int inner = _result;
      _stack.emplace_back(
          _Enter{inner, (((m - 1u) > m ? 0 : (m - 1u))), fuel_});
    }
  }
  return _result;
}

unsigned int LoopifyClassics::ack(const unsigned int &m,
                                  const unsigned int &n) {
  return ack_fuel(((100u * (m + 1u)) * (n + 1u)), m, n);
}

unsigned int LoopifyClassics::binomial_fuel(const unsigned int &fuel,
                                            const unsigned int &n,
                                            const unsigned int &k) {
  struct _Enter {
    unsigned int k;
    unsigned int n;
    unsigned int fuel;
  };

  /// Intermediate: saves [_s0, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s1;
    unsigned int fuel_;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{k, n, fuel});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &k = _f.k;
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if ((k == 0u || k == n)) {
          _result = 1u;
        } else {
          _stack.emplace_back(_After2{(((k - 1u) > k ? 0 : (k - 1u))),
                                      (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
          _stack.emplace_back(
              _Enter{k, (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyClassics::binomial(const unsigned int &n,
                                       const unsigned int &k) {
  return binomial_fuel((n * k), n, k);
}

unsigned int LoopifyClassics::pascal_fuel(const unsigned int &fuel,
                                          const unsigned int &row,
                                          const unsigned int &col) {
  struct _Enter {
    unsigned int col;
    unsigned int row;
    unsigned int fuel;
  };

  /// Intermediate: saves [_s0, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s1;
    unsigned int fuel_;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine1 {
    unsigned int _result;
  };

  using _Frame = std::variant<_Enter, _After2, _Combine1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{col, row, fuel});
  /// Frame dispatch: _Enter, _After2, _Combine1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &col = _f.col;
      const unsigned int &row = _f.row;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if ((col == 0u || col == row)) {
          _result = 1u;
        } else {
          _stack.emplace_back(_After2{(((col - 1u) > col ? 0 : (col - 1u))),
                                      (((row - 1u) > row ? 0 : (row - 1u))),
                                      fuel_});
          _stack.emplace_back(
              _Enter{col, (((row - 1u) > row ? 0 : (row - 1u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine1{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine1>(_frame));
      _result = (_result + _f._result);
    }
  }
  return _result;
}

unsigned int LoopifyClassics::pascal(const unsigned int &row,
                                     const unsigned int &col) {
  return pascal_fuel((row * col), row, col);
}

unsigned int LoopifyClassics::gcd_fuel(const unsigned int &fuel, unsigned int a,
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
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_b == 0u) {
        _result = _loop_a;
        break;
      } else {
        unsigned int _next_b = (_loop_b ? _loop_a % _loop_b : _loop_a);
        unsigned int _next_a = _loop_b;
        unsigned int _next_fuel = fuel_;
        _loop_b = std::move(_next_b);
        _loop_a = std::move(_next_a);
        _loop_fuel = std::move(_next_fuel);
      }
    }
  }
  return _result;
}

unsigned int LoopifyClassics::gcd(const unsigned int &a,
                                  const unsigned int &b) {
  return gcd_fuel((a + b), a, b);
}

unsigned int LoopifyClassics::power(const unsigned int &base,
                                    const unsigned int &exp) {
  struct _Enter {
    unsigned int exp;
  };

  /// Continuation: saves [base] across recursive call.
  struct _Resume1 {
    unsigned int base;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{exp});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &exp = _f.exp;
      if (exp <= 0) {
        _result = 1u;
      } else {
        unsigned int exp_ = exp - 1;
        _stack.emplace_back(_Resume1{base});
        _stack.emplace_back(_Enter{exp_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.base * _result);
    }
  }
  return _result;
}

unsigned int LoopifyClassics::sum_to(const unsigned int &n) {
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
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Resume1{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n + _result);
    }
  }
  return _result;
}

unsigned int LoopifyClassics::sum_squares(const unsigned int &n) {
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
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Resume1{(n * n)});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
