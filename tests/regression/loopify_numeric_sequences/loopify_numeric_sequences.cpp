#include "loopify_numeric_sequences.h"

uint64_t LoopifyNumericSequences::collatz_length_fuel(uint64_t fuel,
                                                      uint64_t n) {
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
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
            _stack.emplace_back(_after_collatz_length_fuel_in_true{});
            _stack.emplace_back(
                _call{(UINT64_C(2) ? n / UINT64_C(2) : 0), fuel_});
          } else {
            _stack.emplace_back(_after_collatz_length_fuel_in_false{});
            _stack.emplace_back(_call{((UINT64_C(3) * n) + UINT64_C(1)),
                                      fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_after_collatz_length_fuel_in_false>(
                   _popped)) {
      auto _f =
          std::move(std::get<_after_collatz_length_fuel_in_false>(_popped));
      _result = (UINT64_C(1) + std::move(_result));
    } else {
      auto _f =
          std::move(std::get<_after_collatz_length_fuel_in_true>(_popped));
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
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  uint64_t _loop_fuel = fuel;
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
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
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

uint64_t LoopifyNumericSequences::tribonacci_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of tribonacci_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_tribonacci_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_tribonacci_fuel_in_false_2 {
    uint64_t n;
    uint64_t fuel_;
    uint64_t _tmp3;
  };

  struct _after_tribonacci_fuel_in_false_3 {
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_tribonacci_fuel_in_false,
                              _after_tribonacci_fuel_in_false_2,
                              _after_tribonacci_fuel_in_false_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
              _stack.emplace_back(_after_tribonacci_fuel_in_false{n, fuel_});
              _stack.emplace_back(_call{
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_after_tribonacci_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_tribonacci_fuel_in_false>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(
          _after_tribonacci_fuel_in_false_2{n, fuel_, std::move(_result)});
      _stack.emplace_back(
          _call{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (
            std::holds_alternative<_after_tribonacci_fuel_in_false_2>(_popped)) {
      auto _f = std::move(std::get<_after_tribonacci_fuel_in_false_2>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(
          _after_tribonacci_fuel_in_false_3{_f._tmp3, std::move(_result)});
      _stack.emplace_back(
          _call{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<_after_tribonacci_fuel_in_false_3>(_popped));
      _result = ((_f._tmp3 + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::tribonacci(uint64_t n) {
  return tribonacci_fuel((n * UINT64_C(3)), n);
}

uint64_t LoopifyNumericSequences::staircase_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of staircase_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_staircase_fuel_in_false {
    uint64_t n;
    uint64_t fuel_;
  };

  struct _after_staircase_fuel_in_false_2 {
    uint64_t n;
    uint64_t fuel_;
    uint64_t _tmp3;
  };

  struct _after_staircase_fuel_in_false_3 {
    uint64_t _tmp3;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_staircase_fuel_in_false,
                              _after_staircase_fuel_in_false_2,
                              _after_staircase_fuel_in_false_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
            _stack.emplace_back(_after_staircase_fuel_in_false{n, fuel_});
            _stack.emplace_back(
                _call{(((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1)))),
                      fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_after_staircase_fuel_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_staircase_fuel_in_false>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(
          _after_staircase_fuel_in_false_2{n, fuel_, std::move(_result)});
      _stack.emplace_back(
          _call{(((n - UINT64_C(2)) > n ? 0 : (n - UINT64_C(2)))), fuel_});
    } else if (
            std::holds_alternative<_after_staircase_fuel_in_false_2>(_popped)) {
      auto _f = std::move(std::get<_after_staircase_fuel_in_false_2>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel_ = _f.fuel_;
      _stack.emplace_back(
          _after_staircase_fuel_in_false_3{_f._tmp3, std::move(_result)});
      _stack.emplace_back(
          _call{(((n - UINT64_C(3)) > n ? 0 : (n - UINT64_C(3)))), fuel_});
    } else {
      auto _f = std::move(std::get<_after_staircase_fuel_in_false_3>(_popped));
      _result = ((_f._tmp3 + _f._tmp2) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::staircase(uint64_t n) {
  return staircase_fuel((n * UINT64_C(3)), n);
}

uint64_t LoopifyNumericSequences::digitsum_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of digitsum_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_digitsum_fuel_in_false {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_digitsum_fuel_in_false>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          _stack.emplace_back(_after_digitsum_fuel_in_false{n});
          _stack.emplace_back(
              _call{(UINT64_C(10) ? n / UINT64_C(10) : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_digitsum_fuel_in_false>(_popped));
      uint64_t n = _f.n;
      _result = ((UINT64_C(10) ? n % UINT64_C(10) : n) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyNumericSequences::digitsum(uint64_t n) {
  return digitsum_fuel((n + UINT64_C(1)), n);
}

uint64_t LoopifyNumericSequences::dec_to_bin_fuel(uint64_t fuel, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of dec_to_bin_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
    uint64_t fuel;
  };

  struct _after_dec_to_bin_fuel_in_false {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_dec_to_bin_fuel_in_false>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n, fuel});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= UINT64_C(0)) {
          _result = UINT64_C(0);
        } else {
          _stack.emplace_back(_after_dec_to_bin_fuel_in_false{n});
          _stack.emplace_back(_call{(UINT64_C(2) ? n / UINT64_C(2) : 0),
                                    fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_dec_to_bin_fuel_in_false>(_popped));
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
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = acc;
  bool _loop_sign = sign;
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

uint64_t LoopifyNumericSequences::sum_divisors_aux(uint64_t n, uint64_t d) {
  // Explicit stack replaces the non-tail recursion of sum_divisors_aux: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t d;
  };

  struct _after_sum_divisors_aux_in_true {
    uint64_t d;
  };

  using _frame = std::variant<_call, _after_sum_divisors_aux_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{d});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      uint64_t d = _f.d;
      if (d <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t d_ = d - 1;
        if ((d ? n % d : n) == UINT64_C(0)) {
          _stack.emplace_back(_after_sum_divisors_aux_in_true{d});
          _stack.emplace_back(_call{d_});
        } else {
          _stack.emplace_back(_call{d_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_sum_divisors_aux_in_true>(_popped));
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
