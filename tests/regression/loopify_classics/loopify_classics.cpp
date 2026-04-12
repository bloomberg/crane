#include <loopify_classics.h>

#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyClassics::factorial(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 1u;
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.emplace_back(_Call1{n});
                              _stack.emplace_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 * _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyClassics::fib(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _After {
    const unsigned int _a0;
  };

  struct _Combine {
    unsigned int _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int n_ = n - 1;
                              if (n_ <= 0) {
                                _result = 1u;
                              } else {
                                unsigned int n__ = n_ - 1;
                                _stack.emplace_back(_After{n_});
                                _stack.emplace_back(_Enter{n__});
                              }
                            }
                          },
                          [&](_After _f) {
                            _stack.emplace_back(_Combine{_result});
                            _stack.emplace_back(_Enter{_f._a0});
                          },
                          [&](_Combine _f) { _result = (_result + _f._left); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyClassics::ack_fuel(const unsigned int fuel, const unsigned int m,
                          const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int m;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    const unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n, m, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const unsigned int n = _f.n;
                     const unsigned int m = _f.m;
                     const unsigned int fuel = _f.fuel;
                     if (fuel <= 0) {
                       _result = (n + 1u);
                     } else {
                       unsigned int fuel_ = fuel - 1;
                       if (m == 0u) {
                         _result = (n + 1u);
                       } else {
                         if (n == 0u) {
                           _stack.emplace_back(_Enter{
                               1u, (((m - 1u) > m ? 0 : (m - 1u))), fuel_});
                         } else {
                           _stack.emplace_back(_Call1{fuel_, m});
                           _stack.emplace_back(_Enter{
                               (((n - 1u) > n ? 0 : (n - 1u))), m, fuel_});
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     unsigned int fuel_ = _f._s0;
                     const unsigned int m = _f._s1;
                     unsigned int inner = _result;
                     _stack.emplace_back(
                         _Enter{inner, (((m - 1u) > m ? 0 : (m - 1u))), fuel_});
                   }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyClassics::ack(const unsigned int m,
                                                        const unsigned int n) {
  return ack_fuel(((100u * (m + 1u)) * (n + 1u)), m, n);
}

__attribute__((pure)) unsigned int
LoopifyClassics::binomial_fuel(const unsigned int fuel, const unsigned int n,
                               const unsigned int k) {
  struct _Enter {
    const unsigned int k;
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
    const unsigned int _a2;
  };

  struct _Combine {
    unsigned int _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{k, n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int k = _f.k;
                            const unsigned int n = _f.n;
                            const unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              _result = 1u;
                            } else {
                              unsigned int fuel_ = fuel - 1;
                              if ((k == 0u || k == n)) {
                                _result = 1u;
                              } else {
                                _stack.emplace_back(_After{
                                    (((k - 1u) > k ? 0 : (k - 1u))),
                                    (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                                _stack.emplace_back(_Enter{
                                    k, (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                              }
                            }
                          },
                          [&](_After _f) {
                            _stack.emplace_back(_Combine{_result});
                            _stack.emplace_back(_Enter{_f._a0, _f._a1, _f._a2});
                          },
                          [&](_Combine _f) { _result = (_result + _f._left); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyClassics::binomial(const unsigned int n, const unsigned int k) {
  return binomial_fuel((n * k), n, k);
}

__attribute__((pure)) unsigned int
LoopifyClassics::pascal_fuel(const unsigned int fuel, const unsigned int row,
                             const unsigned int col) {
  struct _Enter {
    const unsigned int col;
    const unsigned int row;
    const unsigned int fuel;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
    const unsigned int _a2;
  };

  struct _Combine {
    unsigned int _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{col, row, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const unsigned int col = _f.col;
                     const unsigned int row = _f.row;
                     const unsigned int fuel = _f.fuel;
                     if (fuel <= 0) {
                       _result = 1u;
                     } else {
                       unsigned int fuel_ = fuel - 1;
                       if ((col == 0u || col == row)) {
                         _result = 1u;
                       } else {
                         _stack.emplace_back(_After{
                             (((col - 1u) > col ? 0 : (col - 1u))),
                             (((row - 1u) > row ? 0 : (row - 1u))), fuel_});
                         _stack.emplace_back(
                             _Enter{col, (((row - 1u) > row ? 0 : (row - 1u))),
                                    fuel_});
                       }
                     }
                   },
                   [&](_After _f) {
                     _stack.emplace_back(_Combine{_result});
                     _stack.emplace_back(_Enter{_f._a0, _f._a1, _f._a2});
                   },
                   [&](_Combine _f) { _result = (_result + _f._left); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyClassics::pascal(const unsigned int row, const unsigned int col) {
  return pascal_fuel((row * col), row, col);
}

__attribute__((pure)) unsigned int
LoopifyClassics::gcd_fuel(const unsigned int fuel, const unsigned int a,
                          const unsigned int b) {
  unsigned int _result;
  unsigned int _loop_b = b;
  unsigned int _loop_a = a;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = _loop_a;
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_b == 0u) {
        {
          _result = _loop_a;
          _continue = false;
        }
      } else {
        {
          unsigned int _next_b = (_loop_b ? _loop_a % _loop_b : _loop_a);
          unsigned int _next_a = _loop_b;
          unsigned int _next_fuel = fuel_;
          _loop_b = std::move(_next_b);
          _loop_a = std::move(_next_a);
          _loop_fuel = std::move(_next_fuel);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyClassics::gcd(const unsigned int a,
                                                        const unsigned int b) {
  return gcd_fuel((a + b), a, b);
}

__attribute__((pure)) unsigned int
LoopifyClassics::power(const unsigned int base, const unsigned int exp) {
  struct _Enter {
    const unsigned int exp;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{exp});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int exp = _f.exp;
                            if (exp <= 0) {
                              _result = 1u;
                            } else {
                              unsigned int exp_ = exp - 1;
                              _stack.emplace_back(_Call1{base});
                              _stack.emplace_back(_Enter{exp_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 * _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyClassics::sum_to(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.emplace_back(_Call1{n});
                              _stack.emplace_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyClassics::sum_squares(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<const unsigned int &>() *
              std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.emplace_back(_Call1{(n * n)});
                              _stack.emplace_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}
