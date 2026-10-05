#include "loopify_numeric_sequences.h"

uint64_t LoopifyNumericSequences::collatz_length_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified collatz_length_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont1{});
            _stack.emplace_back(
                CraneEnter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
          } else {
            _stack.emplace_back(CraneCont2{});
            _stack.emplace_back(
                CraneEnter{((UINT64_C(3) * n) + UINT64_C(1)), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::collatz_length(uint64_t n) {
  return collatz_length_fuel((n * UINT64_C(100)), n);
}

List<uint64_t> LoopifyNumericSequences::collatz_sequence_fuel(uint64_t fuel,
                                                              uint64_t n) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (_loop_n <= UINT64_C(1)) {
        auto _value = List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        if ((UINT64_C(2) ? _loop_n % UINT64_C(2) : _loop_n) == UINT64_C(0)) {
          auto _cell = typename List<uint64_t>::Cons(_loop_n, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_n = (UINT64_C(2) ? _loop_n / UINT64_C(2) : 0);
          _loop_fuel = fuel_;
          continue;
        } else {
          auto _cell = typename List<uint64_t>::Cons(_loop_n, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_n = ((UINT64_C(3) * _loop_n) + UINT64_C(1));
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyNumericSequences::collatz_sequence(uint64_t n) {
  return collatz_sequence_fuel((n * UINT64_C(100)), n);
}

uint64_t LoopifyNumericSequences::tribonacci_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp3, fuel_, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont2 {
    uint64_t _tmp3;
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont3: saves [_tmp2, _tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont3 {
    uint64_t _tmp2;
    uint64_t _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont1, CraneCont2, CraneCont3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified tribonacci_fuel: CraneEnter -> CraneCont1 -> CraneCont2 ->
  /// CraneCont3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
              _stack.emplace_back(CraneCont1{fuel_, n});
              _stack.emplace_back(CraneEnter{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result), fuel_, n});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont3{std::move(_result), _f._tmp3});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      _result = ((_f._tmp3 + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::tribonacci(uint64_t n) {
  return tribonacci_fuel((n * UINT64_C(3)), n);
}

uint64_t LoopifyNumericSequences::staircase_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [fuel_, n], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont2: saves [_tmp3, fuel_, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont2 {
    uint64_t _tmp3;
    uint64_t fuel_;
    uint64_t n;
  };

  /// CraneCont3: saves [_tmp2, _tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont3 {
    uint64_t _tmp2;
    uint64_t _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont1, CraneCont2, CraneCont3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified staircase_fuel: CraneEnter -> CraneCont1 -> CraneCont2 ->
  /// CraneCont3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont1{fuel_, n});
            _stack.emplace_back(CraneEnter{
                (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont2{std::move(_result), fuel_, n});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t fuel_ = _f.fuel_;
      uint64_t n = _f.n;
      _stack.emplace_back(CraneCont3{std::move(_result), _f._tmp3});
      _stack.emplace_back(
          CraneEnter{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      _result = ((_f._tmp3 + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::staircase(uint64_t n) {
  return staircase_fuel((n * UINT64_C(3)), n);
}

uint64_t LoopifyNumericSequences::digitsum_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified digitsum_fuel: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          _stack.emplace_back(CraneCont1{n});
          _stack.emplace_back(
              CraneEnter{(UINT64_C(10) ? n / UINT64_C(10) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n = _f.n;
      _result = ((UINT64_C(10) ? n % UINT64_C(10) : n) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::digitsum(uint64_t n) {
  return digitsum_fuel((n + UINT64_C(1)), n);
}

uint64_t LoopifyNumericSequences::dec_to_bin_fuel(
    uint64_t fuel, uint64_t n) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    uint64_t n;
    uint64_t fuel;
  };

  /// CraneCont1: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, fuel});
  /// Loopified dec_to_bin_fuel: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          _stack.emplace_back(CraneCont1{n});
          _stack.emplace_back(
              CraneEnter{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t n = _f.n;
      _result = ((UINT64_C(2) ? n % UINT64_C(2) : n) +
                 (UINT64_C(10) * std::move(_result)));
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
    uint64_t n, uint64_t d) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

  struct CraneEnter {
    uint64_t d;
  };

  /// CraneCont1: saves [d], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t d;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{d});
  /// Loopified sum_divisors_aux: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t d = _f.d;
      if (d <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t d_ = d - 1;
        if ((d ? n % d : n) == UINT64_C(0)) {
          _stack.emplace_back(CraneCont1{d});
          _stack.emplace_back(CraneEnter{d_});
        } else {
          _stack.emplace_back(CraneEnter{d_});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t d = _f.d;
      _result = (d + std::move(_result));
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
