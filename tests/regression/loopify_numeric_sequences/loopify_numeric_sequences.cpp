#include "loopify_numeric_sequences.h"

uint64_t LoopifyNumericSequences::collatz_length_fuel(
    uint64_t fuel,
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Cont1: resumes after recursive call, then processes rest.
  struct _Cont1 {};

  /// _Cont2: resumes after recursive call, then processes rest.
  struct _Cont2 {};

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified collatz_length_fuel: _Enter -> _Cont1 -> _Cont2.
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
            _stack.emplace_back(_Cont1{});
            _stack.emplace_back(
                _Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
          } else {
            _stack.emplace_back(_Cont2{});
            _stack.emplace_back(
                _Enter{((UINT64_C(3) * n) + UINT64_C(1)), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t r_ = std::move(_result);
      _result = (UINT64_C(1) + r_);
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t r_ = std::move(_result);
      _result = (UINT64_C(1) + r_);
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::collatz_length(uint64_t n) {
  return collatz_length_fuel((n * UINT64_C(100)), n);
}

List<uint64_t> LoopifyNumericSequences::collatz_sequence_fuel(uint64_t fuel,
                                                              uint64_t n) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(1)) {
        *_write = std::make_shared<List<uint64_t>>(
            List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()));
        break;
      } else {
        if ((UINT64_C(2) ? _loop_n % UINT64_C(2) : _loop_n) == UINT64_C(0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(_loop_n, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_n = (UINT64_C(2) ? _loop_n / UINT64_C(2) : 0);
          _loop_fuel = fuel_;
          continue;
        } else {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(_loop_n, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_n = ((UINT64_C(3) * _loop_n) + UINT64_C(1));
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_head);
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

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [fuel_, n, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont2 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t r_;
  };

  /// _Cont3: saves [r_, r_0], resumes after recursive call, then processes
  /// rest.
  struct _Cont3 {
    uint64_t r_;
    uint64_t r_0;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2, _Cont3>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified tribonacci_fuel: _Enter -> _Cont1 -> _Cont2 -> _Cont3.
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
              _stack.emplace_back(_Cont1{fuel_, n});
              _stack.emplace_back(_Enter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont2{fuel_, n, r_});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<_Cont2>(_frame)) {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _stack.emplace_back(_Cont3{r_, r_0});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont3>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = std::move(_result);
      _result = ((r_ + r_0) + r_1);
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

  /// _Cont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct _Cont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// _Cont2: saves [fuel_, n, r_], resumes after recursive call, then processes
  /// rest.
  struct _Cont2 {
    uint64_t fuel_;
    uint64_t n;
    uint64_t r_;
  };

  /// _Cont3: saves [r_, r_0], resumes after recursive call, then processes
  /// rest.
  struct _Cont3 {
    uint64_t r_;
    uint64_t r_0;
  };

  using _Frame = std::variant<_Enter, _Cont1, _Cont2, _Cont3>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified staircase_fuel: _Enter -> _Cont1 -> _Cont2 -> _Cont3.
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
            _stack.emplace_back(_Cont1{fuel_, n});
            _stack.emplace_back(_Enter{
                (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t r_ = std::move(_result);
      _stack.emplace_back(_Cont2{fuel_, n, r_});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<_Cont2>(_frame)) {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      uint64_t r_ = _f.r_;
      uint64_t r_0 = std::move(_result);
      _stack.emplace_back(_Cont3{r_, r_0});
      _stack.emplace_back(
          _Enter{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<_Cont3>(_frame));
      uint64_t r_ = _f.r_;
      uint64_t r_0 = _f.r_0;
      uint64_t r_1 = std::move(_result);
      _result = ((r_ + r_0) + r_1);
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

  /// _Cont1: saves [n], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified digitsum_fuel: _Enter -> _Cont1.
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
          _stack.emplace_back(_Cont1{n});
          _stack.emplace_back(
              _Enter{(UINT64_C(10) ? n / UINT64_C(10) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t n = _f.n;
      uint64_t r_ = std::move(_result);
      _result = ((UINT64_C(10) ? n % UINT64_C(10) : n) + r_);
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

  /// _Cont1: saves [n], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified dec_to_bin_fuel: _Enter -> _Cont1.
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
          _stack.emplace_back(_Cont1{n});
          _stack.emplace_back(
              _Enter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t n = _f.n;
      uint64_t r_ = std::move(_result);
      _result = ((UINT64_C(2) ? n % UINT64_C(2) : n) + (UINT64_C(10) * r_));
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
        _loop_l = crane_raw(a1);
        _loop_acc = (_loop_acc + a0);
        _loop_sign = false;
      } else {
        if (a0 <= _loop_acc) {
          _loop_l = crane_raw(a1);
          _loop_acc = (((_loop_acc - a0) > _loop_acc ? 0 : (_loop_acc - a0)));
          _loop_sign = true;
        } else {
          _loop_l = crane_raw(a1);
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

  /// _Cont1: saves [d], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t d;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{d});
  /// Loopified sum_divisors_aux: _Enter -> _Cont1.
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
          _stack.emplace_back(_Cont1{d});
          _stack.emplace_back(_Enter{d_});
        } else {
          _stack.emplace_back(_Enter{d_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t d = _f.d;
      uint64_t r_ = std::move(_result);
      _result = (d + r_);
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
