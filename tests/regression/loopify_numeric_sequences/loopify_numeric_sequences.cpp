#include <loopify_numeric_sequences.h>

__attribute__((pure)) unsigned int
LoopifyNumericSequences::collatz_length_fuel(const unsigned int &fuel,
                                             const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  struct _Call2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 1u) {
          _result = 0u;
        } else {
          if ((2u ? n % 2u : n) == 0u) {
            _stack.emplace_back(_Call1{1u});
            _stack.emplace_back(_Enter{(2u ? n / 2u : 0), fuel_});
          } else {
            _stack.emplace_back(_Call2{1u});
            _stack.emplace_back(_Enter{((3u * n) + 1u), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::collatz_length(const unsigned int &n) {
  return collatz_length_fuel((n * 100u), n);
}

__attribute__((pure)) List<unsigned int>
LoopifyNumericSequences::collatz_sequence_fuel(const unsigned int &fuel,
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
          unsigned int _next_n = (2u ? _loop_n / 2u : 0);
          unsigned int _next_fuel = fuel_;
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
          unsigned int _next_fuel = fuel_;
          _loop_n = std::move(_next_n);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyNumericSequences::collatz_sequence(const unsigned int &n) {
  return collatz_sequence_fuel((n * 100u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::tribonacci_fuel(const unsigned int &fuel,
                                         const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
    const unsigned int _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
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
              _stack.emplace_back(_Call1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                         (((n - 1u) > n ? 0 : (n - 1u))),
                                         fuel_});
              _stack.emplace_back(
                  _Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_f._s0, _result});
      _stack.emplace_back(_Enter{_f._s1, _f._s2});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = ((_result + _f._s1) + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::tribonacci(const unsigned int &n) {
  return tribonacci_fuel((n * 3u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::staircase_fuel(const unsigned int &fuel,
                                        const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
    const unsigned int _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 1u;
        } else {
          if (n == 1u) {
            _result = 1u;
          } else {
            _stack.emplace_back(_Call1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                       (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
            _stack.emplace_back(_Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_f._s0, _result});
      _stack.emplace_back(_Enter{_f._s1, _f._s2});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = ((_result + _f._s1) + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::staircase(const unsigned int &n) {
  return staircase_fuel((n * 3u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::digitsum_fuel(const unsigned int &fuel,
                                       const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((10u ? std::declval<const unsigned int &>() % 10u
                  : std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          _stack.emplace_back(_Call1{(10u ? n % 10u : n)});
          _stack.emplace_back(_Enter{(10u ? n / 10u : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::digitsum(const unsigned int &n) {
  return digitsum_fuel((n + 1u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::dec_to_bin_fuel(const unsigned int &fuel,
                                         const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((2u ? std::declval<const unsigned int &>() % 2u
                 : std::declval<const unsigned int &>())) _s0;
    decltype(10u) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
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
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          _stack.emplace_back(_Call1{(2u ? n % 2u : n), 10u});
          _stack.emplace_back(_Enter{(2u ? n / 2u : 0), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + (_f._s1 * _result));
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::dec_to_bin(const unsigned int &n) {
  return dec_to_bin_fuel((n + 1u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::alternate_sum(const bool &sign, unsigned int acc,
                                       const List<unsigned int> &l) {
  unsigned int _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = std::move(acc);
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
        const List<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_acc = (_loop_acc + d_a0);
        bool _next_sign = false;
        _loop_l = _next_l;
        _loop_acc = std::move(_next_acc);
        _loop_sign = std::move(_next_sign);
      } else {
        if (d_a0 <= _loop_acc) {
          const List<unsigned int> *_next_l = d_a1.get();
          unsigned int _next_acc =
              (((_loop_acc - d_a0) > _loop_acc ? 0 : (_loop_acc - d_a0)));
          bool _next_sign = true;
          _loop_l = _next_l;
          _loop_acc = std::move(_next_acc);
          _loop_sign = std::move(_next_sign);
        } else {
          const List<unsigned int> *_next_l = d_a1.get();
          unsigned int _next_acc = 0u;
          bool _next_sign = true;
          _loop_l = _next_l;
          _loop_acc = std::move(_next_acc);
          _loop_sign = std::move(_next_sign);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::sum_divisors_aux(const unsigned int &n,
                                          const unsigned int &d) {
  struct _Enter {
    const unsigned int d;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{d});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &d = _f.d;
      if (d <= 0) {
        _result = 0u;
      } else {
        unsigned int d_ = d - 1;
        if ((d ? n % d : n) == 0u) {
          _stack.emplace_back(_Call1{d});
          _stack.emplace_back(_Enter{d_});
        } else {
          _stack.emplace_back(_Enter{d_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::sum_divisors(const unsigned int &n) {
  if (n <= 1u) {
    return 0u;
  } else {
    return sum_divisors_aux(n, (((n - 1u) > n ? 0 : (n - 1u))));
  }
}
