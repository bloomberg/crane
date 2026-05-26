#include "loopify_numeric_sequences.h"

uint64_t LoopifyNumericSequences::collatz_length_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    std::decay_t<decltype(UINT64_C(1))> _s0;
  };

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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(1)) {
          _result = UINT64_C(0);
        } else {
          if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
            _stack.emplace_back(_Resume1{UINT64_C(1)});
            _stack.emplace_back(
                _Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
          } else {
            _stack.emplace_back(_Resume2{UINT64_C(1)});
            _stack.emplace_back(
                _Enter{((UINT64_C(3) * n) + UINT64_C(1)), fuel_});
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

uint64_t LoopifyNumericSequences::collatz_length(uint64_t n) {
  return collatz_length_fuel((n * UINT64_C(100)), n);
}

List<uint64_t> LoopifyNumericSequences::collatz_sequence_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: saves [n], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t n;
  };

  /// _Resume2: saves [n], resumes after recursive call with _result.
  struct _Resume2 {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified collatz_sequence_fuel: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(1)) {
          _result = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
        } else {
          if ((UINT64_C(2) ? n % UINT64_C(2) : n) == UINT64_C(0)) {
            _stack.emplace_back(_Resume1{n});
            _stack.emplace_back(
                _Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
          } else {
            _stack.emplace_back(_Resume2{n});
            _stack.emplace_back(
                _Enter{((UINT64_C(3) * n) + UINT64_C(1)), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.n, _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = List<uint64_t>::cons(_f.n, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyNumericSequences::collatz_sequence(uint64_t n) {
  return collatz_sequence_fuel((n * UINT64_C(100)), n);
}

uint64_t LoopifyNumericSequences::tribonacci_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After1: saves [_s0, fuel__0, _s2, fuel__1], dispatches next recursive
  /// call.
  struct _After1 {
    uint64_t _s0;
    uint64_t fuel__0;
    uint64_t _s2;
    uint64_t fuel__1;
  };

  /// _After2: saves [_result, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    uint64_t _result;
    uint64_t _s1;
    uint64_t fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    uint64_t _result_0;
    uint64_t _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified tribonacci_fuel: _Enter -> _After1 -> _After2 -> _Combine3.
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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          if (n == UINT64_C(1)) {
            _result = UINT64_C(0);
          } else {
            if (n == UINT64_C(2)) {
              _result = UINT64_C(1);
            } else {
              _stack.emplace_back(_After1{
                  (((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_,
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
              _stack.emplace_back(_Enter{
                  (((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
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
      _result = ((std::move(_result) + _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::tribonacci(uint64_t n) {
  return tribonacci_fuel((n * UINT64_C(3)), n);
}

uint64_t LoopifyNumericSequences::staircase_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _After1: saves [_s0, fuel__0, _s2, fuel__1], dispatches next recursive
  /// call.
  struct _After1 {
    uint64_t _s0;
    uint64_t fuel__0;
    uint64_t _s2;
    uint64_t fuel__1;
  };

  /// _After2: saves [_result, _s1, fuel_], dispatches next recursive call.
  struct _After2 {
    uint64_t _result;
    uint64_t _s1;
    uint64_t fuel_;
  };

  /// _Combine3: receives partial results, combines with _result from final
  /// call.
  struct _Combine3 {
    uint64_t _result_0;
    uint64_t _result_1;
  };

  using _Frame = std::variant<_Enter, _After1, _After2, _Combine3>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified staircase_fuel: _Enter -> _After1 -> _After2 -> _Combine3.
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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(1);
        } else {
          if (n == UINT64_C(1)) {
            _result = UINT64_C(1);
          } else {
            _stack.emplace_back(_After1{
                (((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_,
                (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            _stack.emplace_back(_Enter{
                (((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
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
      _result = ((std::move(_result) + _f._result_1) + _f._result_0);
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::staircase(uint64_t n) {
  return staircase_fuel((n * UINT64_C(3)), n);
}

uint64_t LoopifyNumericSequences::digitsum_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: saves [_s0], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype((UINT64_C(10)
                               ? std::declval<uint64_t &>() % UINT64_C(10)
                               : std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified digitsum_fuel: _Enter -> _Resume1.
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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          _stack.emplace_back(_Resume1{(UINT64_C(10) ? n % UINT64_C(10) : n)});
          _stack.emplace_back(
              _Enter{(UINT64_C(10) ? n / UINT64_C(10) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::digitsum(uint64_t n) {
  return digitsum_fuel((n + UINT64_C(1)), n);
}

uint64_t LoopifyNumericSequences::dec_to_bin_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume1: saves [_s0, _s1], resumes after recursive call with _result.
  struct _Resume1 {
    std::decay_t<decltype((UINT64_C(2)
                               ? std::declval<uint64_t &>() % UINT64_C(2)
                               : std::declval<uint64_t &>()))>
        _s0;
    std::decay_t<decltype(UINT64_C(10))> _s1;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified dec_to_bin_fuel: _Enter -> _Resume1.
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
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          _stack.emplace_back(
              _Resume1{(UINT64_C(2) ? n % UINT64_C(2) : n), UINT64_C(10)});
          _stack.emplace_back(
              _Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 + (_f._s1 * _result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::dec_to_bin(uint64_t n) {
  return dec_to_bin_fuel((n + UINT64_C(1)), n);
}

uint64_t LoopifyNumericSequences::alternate_sum(bool sign, uint64_t acc,
                                                const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  bool _loop_sign = std::move(sign);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_sign) {
        _loop_l = a1.get();
        _loop_acc = (_loop_acc + a0);
        _loop_sign = false;
      } else {
        if (a0 <= _loop_acc) {
          _loop_l = a1.get();
          _loop_acc = (((_loop_acc - a0) > _loop_acc ? 0 : (_loop_acc - a0)));
          _loop_sign = true;
        } else {
          _loop_l = a1.get();
          _loop_acc = UINT64_C(0);
          _loop_sign = true;
        }
      }
    }
  }
}

uint64_t LoopifyNumericSequences::sum_divisors_aux(
    uint64_t n,
    uint64_t
        d) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t d;
  };

  /// _Resume1: saves [d], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t d;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{d});
  /// Loopified sum_divisors_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t d = _f.d;
      if (d <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t d_ = d - 1;
        if ((d ? n % d : n) == UINT64_C(0)) {
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

uint64_t LoopifyNumericSequences::sum_divisors(uint64_t n) {
  if (n <= UINT64_C(1)) {
    return UINT64_C(0);
  } else {
    return sum_divisors_aux(n,
                            (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))));
  }
}
