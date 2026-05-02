#include <loopify_numeric_sequences.h>

unsigned int LoopifyNumericSequences::collatz_length_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    decltype(1u) _s0;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 1u) {
          _result = 0u;
        } else {
          if ((2u ? n % 2u : n) == 0u) {
            _stack.emplace_back(_Resume1{1u});
            _stack.emplace_back(_Enter{(2u ? n / 2u : 0), fuel_});
          } else {
            _stack.emplace_back(_Resume2{1u});
            _stack.emplace_back(_Enter{((3u * n) + 1u), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::collatz_length(const unsigned int n) {
  return collatz_length_fuel((n * 100u), n);
}

List<unsigned int>
LoopifyNumericSequences::collatz_sequence_fuel(const unsigned int fuel,
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
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 1u) {
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
          _loop_fuel = fuel_;
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(_loop_n, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_n = ((3u * _loop_n) + 1u);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int>
LoopifyNumericSequences::collatz_sequence(const unsigned int n) {
  return collatz_sequence_fuel((n * 100u), n);
}

unsigned int LoopifyNumericSequences::tribonacci_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After1: saves [_s0, fuel__0, _s2, fuel__1], dispatches next recursive
  /// call.
  struct _After1 {
    unsigned int _s0;
    unsigned int fuel__0;
    unsigned int _s2;
    unsigned int fuel__1;
  };

  /// _After2: saves [_result, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified tribonacci_fuel: _Enter -> _After1 -> _After2 -> _Combine3.
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          if (n == 1u) {
            _result = 0u;
          } else {
            if (n == 2u) {
              _result = 1u;
            } else {
              _stack.emplace_back(
                  _After1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                          (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
              _stack.emplace_back(
                  _Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_After1>(_frame)) {
      auto _f = std::move(std::get<_After1>(_frame));
      _stack.emplace_back(_After2{_result, _f._s2, _f.fuel__1});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel__0});
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine3{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = ((_result + _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::tribonacci(const unsigned int n) {
  return tribonacci_fuel((n * 3u), n);
}

unsigned int LoopifyNumericSequences::staircase_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _After1: saves [_s0, fuel__0, _s2, fuel__1], dispatches next recursive
  /// call.
  struct _After1 {
    unsigned int _s0;
    unsigned int fuel__0;
    unsigned int _s2;
    unsigned int fuel__1;
  };

  /// _After2: saves [_result, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    unsigned int _result;
    unsigned int _s1;
    unsigned int fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    unsigned int _result_0;
    unsigned int _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified staircase_fuel: _Enter -> _After1 -> _After2 -> _Combine3.
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 1u;
        } else {
          if (n == 1u) {
            _result = 1u;
          } else {
            _stack.emplace_back(_After1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                        (((n - 1u) > n ? 0 : (n - 1u))),
                                        fuel_});
            _stack.emplace_back(_Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_After1>(_frame)) {
      auto _f = std::move(std::get<_After1>(_frame));
      _stack.emplace_back(_After2{_result, _f._s2, _f.fuel__1});
      _stack.emplace_back(_Enter{_f._s0, _f.fuel__0});
    } else if (std::holds_alternative<_After2>(_frame)) {
      auto _f = std::move(std::get<_After2>(_frame));
      _stack.emplace_back(_Combine3{_f._result, _result});
      _stack.emplace_back(_Enter{_f._s1, _f.fuel_});
    } else {
      auto _f = std::move(std::get<_Combine3>(_frame));
      _result = ((_result + _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::staircase(const unsigned int n) {
  return staircase_fuel((n * 3u), n);
}

unsigned int LoopifyNumericSequences::digitsum_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    decltype((10u ? std::declval<const unsigned int &>() % 10u
                  : std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified digitsum_fuel: _Enter -> _Resume1.
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          _stack.emplace_back(_Resume1{(10u ? n % 10u : n)});
          _stack.emplace_back(_Enter{(10u ? n / 10u : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::digitsum(const unsigned int n) {
  return digitsum_fuel((n + 1u), n);
}

unsigned int LoopifyNumericSequences::dec_to_bin_fuel(
    const unsigned int fuel,
    const unsigned int
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume1: saves [_s0, _s1], resumes after recursive call with _result.
  struct _Resume1 {
    decltype((2u ? std::declval<const unsigned int &>() % 2u
                 : std::declval<const unsigned int &>())) _s0;
    decltype(10u) _s1;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified dec_to_bin_fuel: _Enter -> _Resume1.
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          _stack.emplace_back(_Resume1{(2u ? n % 2u : n), 10u});
          _stack.emplace_back(_Enter{(2u ? n / 2u : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + (_f._s1 * _result));
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::dec_to_bin(const unsigned int n) {
  return dec_to_bin_fuel((n + 1u), n);
}

unsigned int
LoopifyNumericSequences::alternate_sum(const bool sign, const unsigned int acc,
                                       const List<unsigned int> &l) {
  unsigned int _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = acc;
  bool _loop_sign = sign;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_sign) {
        _loop_l = d_a1.get();
        _loop_acc = (_loop_acc + d_a0);
        _loop_sign = false;
      } else {
        if (d_a0 <= _loop_acc) {
          _loop_l = d_a1.get();
          _loop_acc =
              (((_loop_acc - d_a0) > _loop_acc ? 0 : (_loop_acc - d_a0)));
          _loop_sign = true;
        } else {
          _loop_l = d_a1.get();
          _loop_acc = 0u;
          _loop_sign = true;
        }
      }
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::sum_divisors_aux(
    const unsigned int n,
    const unsigned int
        d) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int d;
  };

  /// _Resume1: saves [d], resumes after recursive call with _result.
  struct _Resume1 {
    unsigned int d;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{d});
  /// Loopified sum_divisors_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int d = _f.d;
      if (d <= 0) {
        _result = 0u;
      } else {
        unsigned int d_ = d - 1;
        if ((d ? n % d : n) == 0u) {
          _stack.emplace_back(_Resume1{d});
          _stack.emplace_back(_Enter{d_});
        } else {
          _stack.emplace_back(_Enter{d_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.d + _result);
    }
  }
  return _result;
}

unsigned int LoopifyNumericSequences::sum_divisors(const unsigned int n) {
  if (n <= 1u) {
    return 0u;
  } else {
    return sum_divisors_aux(n, (((n - 1u) > n ? 0 : (n - 1u))));
  }
}
