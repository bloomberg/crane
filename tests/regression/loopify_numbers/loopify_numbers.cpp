#include <loopify_numbers.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

/// Consolidated UNIQUE numeric algorithms - no basic arithmetic.
/// Tests loopification on number theory and recursive sequences.
__attribute__((pure)) unsigned int
LoopifyNumbers::factorial(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 1u;
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{n});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 * _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyNumbers::fib(const unsigned int n) {
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
  _stack.push_back(_Enter{n});
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
                                unsigned int m = n_ - 1;
                                _stack.push_back(_After{n_});
                                _stack.push_back(_Enter{m});
                              }
                            }
                          },
                          [&](_After _f) {
                            _stack.push_back(_Combine{_result});
                            _stack.push_back(_Enter{_f._a0});
                          },
                          [&](_Combine _f) { _result = (_result + _f._left); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::tribonacci_fuel(const unsigned int fuel, const unsigned int n) {
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
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
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
                             _stack.push_back(
                                 _Call1{(m + 1), f, ((m + 1) + 1), f});
                             _stack.push_back(_Enter{m, f});
                           }
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     _stack.push_back(_Call2{_result, _f._s2, _f._s3});
                     _stack.push_back(_Enter{_f._s0, _f._s1});
                   },
                   [&](_Call2 _f) {
                     _stack.push_back(_Call3{_f._s0, _result});
                     _stack.push_back(_Enter{_f._s1, _f._s2});
                   },
                   [&](_Call3 _f) { _result = (_result + (_f._s1 + _f._s0)); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::tribonacci(const unsigned int n) {
  return tribonacci_fuel(100u, n);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::gcd_fuel(const unsigned int fuel, const unsigned int a,
                         const unsigned int b) {
  unsigned int _result;
  unsigned int _loop_b = b;
  unsigned int _loop_a = a;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = std::move(_loop_a);
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_b <= 0) {
        {
          _result = _loop_a;
          _continue = false;
        }
      } else {
        unsigned int _x = _loop_b - 1;
        {
          unsigned int _next_b = (_loop_a % _loop_b);
          unsigned int _next_a = _loop_b;
          unsigned int _next_fuel = std::move(f);
          _loop_b = std::move(_next_b);
          _loop_a = std::move(_next_a);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyNumbers::gcd(const unsigned int a,
                                                       const unsigned int b) {
  return gcd_fuel((a + b), a, b);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::binomial(const unsigned int n, const unsigned int k) {
  struct _Enter {
    const unsigned int k;
    const unsigned int n;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
  };

  struct _Combine {
    unsigned int _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{k, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
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
                                _stack.push_back(_After{k_, n_});
                                _stack.push_back(_Enter{k, n_});
                              }
                            }
                          },
                          [&](_After _f) {
                            _stack.push_back(_Combine{_result});
                            _stack.push_back(_Enter{_f._a0, _f._a1});
                          },
                          [&](_Combine _f) { _result = (_result + _f._left); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::pascal(const unsigned int row, const unsigned int col) {
  struct _Enter {
    const unsigned int col;
    const unsigned int row;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
  };

  struct _Combine {
    unsigned int _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{col, row});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
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
                                _stack.push_back(_After{c, r});
                                _stack.push_back(_Enter{(c + 1), r});
                              }
                            }
                          },
                          [&](_After _f) {
                            _stack.push_back(_Combine{_result});
                            _stack.push_back(_Enter{_f._a0, _f._a1});
                          },
                          [&](_Combine _f) { _result = (_result + _f._left); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::ackermann_fuel(const unsigned int fuel, const unsigned int m,
                               const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int m;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, m, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
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
                                  _stack.push_back(
                                      _Enter{1u, std::move(m_), f});
                                } else {
                                  unsigned int n_ = n - 1;
                                  _stack.push_back(_Call1{m_, f});
                                  _stack.push_back(_Enter{std::move(n_), m, f});
                                }
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            _stack.push_back(_Enter{_result, _f._s0, _f._s1});
                          }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyNumbers::ack(const unsigned int m,
                                                       const unsigned int n) {
  return ackermann_fuel(1000u, m, n);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::collatz_length_fuel(const unsigned int fuel,
                                    const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {};

  struct _Call2 {};

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            const unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int f = fuel - 1;
                              if (n == 1u) {
                                _result = 0u;
                              } else {
                                if ((n % 2u) == 0u) {
                                  _stack.push_back(_Call1{});
                                  _stack.push_back(
                                      _Enter{Nat::div(n, 2u), std::move(f)});
                                } else {
                                  _stack.push_back(_Call2{});
                                  _stack.push_back(
                                      _Enter{((3u * n) + 1u), std::move(f)});
                                }
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_result + 1); },
                          [&](_Call2 _f) { _result = (_result + 1); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::collatz_length(const unsigned int n) {
  return collatz_length_fuel(1000u, n);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::digitsum_fuel(const unsigned int fuel, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((std::declval<const unsigned int &>() % 10u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
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
                                _stack.push_back(_Call1{(n % 10u)});
                                _stack.push_back(_Enter{Nat::div(n, 10u), f});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::digitsum(const unsigned int n) {
  return digitsum_fuel(100u, n);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::dec_to_bin_fuel(const unsigned int fuel, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
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
                                unsigned int digit = (n % 2u);
                                _stack.push_back(_Call1{digit});
                                _stack.push_back(_Enter{Nat::div(n, 2u), f});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            unsigned int digit = _f._s0;
                            unsigned int rest = _result;
                            _result =
                                (std::move(digit) + (10u * std::move(rest)));
                          }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::dec_to_bin(const unsigned int n) {
  return dec_to_bin_fuel(100u, n);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_to(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{n});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_squares(const unsigned int n) {
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
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{(n * n)});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::alternating_sum(const bool sign, const unsigned int acc,
                                const unsigned int n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_acc = acc;
  bool _loop_sign = sign;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = std::move(_loop_acc);
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      unsigned int new_acc;
      if (_loop_sign) {
        new_acc = (_loop_acc + std::move(_loop_n));
      } else {
        new_acc = (((_loop_acc - std::move(_loop_n)) > _loop_acc
                        ? 0
                        : (_loop_acc - std::move(_loop_n))));
      }
      {
        unsigned int _next_n = m;
        unsigned int _next_acc = std::move(new_acc);
        bool _next_sign = !(_loop_sign);
        _loop_n = std::move(_next_n);
        _loop_acc = std::move(_next_acc);
        _loop_sign = std::move(_next_sign);
        continue;
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::staircase_fuel(const unsigned int fuel, const unsigned int n) {
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
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
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
                             _stack.push_back(
                                 _Call1{(m + 1), f, ((m + 1) + 1), f});
                             _stack.push_back(_Enter{m, f});
                           }
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     _stack.push_back(_Call2{_result, _f._s2, _f._s3});
                     _stack.push_back(_Enter{_f._s0, _f._s1});
                   },
                   [&](_Call2 _f) {
                     _stack.push_back(_Call3{_f._s0, _result});
                     _stack.push_back(_Enter{_f._s1, _f._s2});
                   },
                   [&](_Call3 _f) { _result = (_result + (_f._s1 + _f._s0)); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::staircase(const unsigned int n) {
  return staircase_fuel(100u, n);
}

/// iterate_pred n applies predecessor n times, starting from n.
/// Tests church-style iteration with concrete function.
__attribute__((pure)) unsigned int
LoopifyNumbers::iterate_pred(const unsigned int n) {
  return church(
      n,
      [](unsigned int x) {
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
__attribute__((pure)) unsigned int
LoopifyNumbers::sum_while_positive(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{n});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

/// count_down_by k n counts down from n by steps of k.
/// Tests recursion with non-standard step size.
__attribute__((pure)) unsigned int
LoopifyNumbers::count_down_by_fuel(const unsigned int fuel,
                                   const unsigned int k, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
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
                                  _stack.push_back(_Call1{});
                                  _stack.push_back(
                                      _Enter{(((n - k) > n ? 0 : (n - k))),
                                             std::move(f)});
                                }
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_result + 1); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::count_down_by(const unsigned int k, const unsigned int n) {
  return count_down_by_fuel(100u, k, n);
}

/// mixed_arith n combines multiplication and addition in recursion.
__attribute__((pure)) unsigned int
LoopifyNumbers::mixed_arith_fuel(const unsigned int fuel,
                                 const unsigned int n) {
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
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
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
                             _stack.push_back(_Call1{m, f, n_, f});
                             _stack.push_back(_Enter{
                                 [&](void) {
                                   if (m == 0u) {
                                     return 0u;
                                   } else {
                                     return (((m - 1u) > m ? 0 : (m - 1u)));
                                   }
                                 }(),
                                 f});
                           }
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     _stack.push_back(_Call2{_result, _f._s2, _f._s3});
                     _stack.push_back(_Enter{_f._s0, _f._s1});
                   },
                   [&](_Call2 _f) {
                     _stack.push_back(_Call3{_f._s0, _result});
                     _stack.push_back(_Enter{_f._s1, _f._s2});
                   },
                   [&](_Call3 _f) { _result = ((_result * _f._s1) + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::mixed_arith(const unsigned int n) {
  return mixed_arith_fuel(1000u, n);
}

/// is_even n checks if n is even (mutually recursive with is_odd).
__attribute__((pure)) bool LoopifyNumbers::is_even_fuel(const unsigned int fuel,
                                                        const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = true;
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        {
          _result = true;
          _continue = false;
        }
      } else {
        const unsigned int _inl_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        const unsigned int _inl_fuel = f;
        if (_inl_fuel <= 0) {
          {
            _result = false;
            _continue = false;
          }
        } else {
          unsigned int f = _inl_fuel - 1;
          if (_inl_n == 0u) {
            {
              _result = false;
              _continue = false;
            }
          } else {
            {
              unsigned int _next_n =
                  (((_inl_n - 1u) > _inl_n ? 0 : (_inl_n - 1u)));
              unsigned int _next_fuel = f;
              _loop_n = std::move(_next_n);
              _loop_fuel = std::move(_next_fuel);
              continue;
            }
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool LoopifyNumbers::is_odd_fuel(const unsigned int fuel,
                                                       const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = false;
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        {
          _result = false;
          _continue = false;
        }
      } else {
        const unsigned int _inl_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        const unsigned int _inl_fuel = f;
        if (_inl_fuel <= 0) {
          {
            _result = true;
            _continue = false;
          }
        } else {
          unsigned int f = _inl_fuel - 1;
          if (_inl_n == 0u) {
            {
              _result = true;
              _continue = false;
            }
          } else {
            {
              unsigned int _next_n =
                  (((_inl_n - 1u) > _inl_n ? 0 : (_inl_n - 1u)));
              unsigned int _next_fuel = f;
              _loop_n = std::move(_next_n);
              _loop_fuel = std::move(_next_fuel);
              continue;
            }
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool LoopifyNumbers::is_even(const unsigned int n) {
  return is_even_fuel(1000u, n);
}

__attribute__((pure)) bool LoopifyNumbers::is_odd(const unsigned int n) {
  return is_odd_fuel(1000u, n);
}

/// power b e computes b^e.
__attribute__((pure)) unsigned int LoopifyNumbers::power(const unsigned int b,
                                                         const unsigned int e) {
  struct _Enter {
    const unsigned int e;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int e = _f.e;
                            if (e <= 0) {
                              _result = 1u;
                            } else {
                              unsigned int e_ = e - 1;
                              _stack.push_back(_Call1{b});
                              _stack.push_back(_Enter{e_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 * _result); }},
               _frame);
  }
  return _result;
}

/// power_mod b e m computes (b^e) mod m efficiently.
__attribute__((pure)) unsigned int
LoopifyNumbers::power_mod_fuel(const unsigned int fuel, const unsigned int b,
                               const unsigned int e, const unsigned int m) {
  struct _Enter {
    const unsigned int e;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  struct _Call2 {
    const unsigned int _s0;
    const unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int e = _f.e;
                            const unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int f = fuel - 1;
                              if (e == 0u) {
                                _result = 1u;
                              } else {
                                if ((e % 2u) == 0u) {
                                  _stack.push_back(_Call1{m});
                                  _stack.push_back(_Enter{Nat::div(e, 2u), f});
                                } else {
                                  _stack.push_back(_Call2{b, m});
                                  _stack.push_back(_Enter{Nat::div(e, 2u), f});
                                }
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            const unsigned int m = _f._s0;
                            unsigned int half = _result;
                            _result = ((half * half) % m);
                          },
                          [&](_Call2 _f) {
                            const unsigned int b = _f._s0;
                            const unsigned int m = _f._s1;
                            unsigned int half = _result;
                            _result = ((b * (half * half)) % m);
                          }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::power_mod(const unsigned int b, const unsigned int e,
                          const unsigned int m) {
  return power_mod_fuel(1000u, b, e, m);
}

/// sum_divisors n sums all divisors of n (excluding n itself).
__attribute__((pure)) unsigned int
LoopifyNumbers::sum_divisors_aux(const unsigned int n, const unsigned int k) {
  struct _Enter {
    const unsigned int k;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{k});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int k = _f.k;
                            if (k <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int k_ = k - 1;
                              if (k_ <= 0) {
                                _result = 0u;
                              } else {
                                unsigned int _x = k_ - 1;
                                if ((n % k) == 0u) {
                                  _stack.push_back(_Call1{k});
                                  _stack.push_back(_Enter{k_});
                                } else {
                                  _stack.push_back(_Enter{k_});
                                }
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_divisors(const unsigned int n) {
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
__attribute__((pure)) unsigned int LoopifyNumbers::sum_odd_indices_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  if (fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = fuel - 1;
    return std::visit(
        Overloaded{
            [](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return 0u;
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              return (_args.d_a0 + sum_even_indices_fuel(f, _args.d_a1));
            }},
        l->v());
  }
}

__attribute__((pure)) unsigned int LoopifyNumbers::sum_even_indices_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = 0u;
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void { _result = 0u; },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          {
                            const std::shared_ptr<List<unsigned int>> &_inl_l =
                                _args.d_a1;
                            const unsigned int _inl_fuel = f;
                            if (_inl_fuel <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int f = _inl_fuel - 1;
                              std::visit(
                                  Overloaded{
                                      [&](const typename List<unsigned int>::Nil
                                              _args) -> void { _result = 0u; },
                                      [&](const typename List<
                                          unsigned int>::Cons _args) -> void {
                                        _stack.push_back(_Call1{_args.d_a0});
                                        _stack.push_back(_Enter{_args.d_a1, f});
                                      }},
                                  _inl_l->v());
                            }
                          }
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_odd_indices(const std::shared_ptr<List<unsigned int>> &l) {
  return sum_odd_indices_fuel(l->length(), l);
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_even_indices(const std::shared_ptr<List<unsigned int>> &l) {
  return sum_even_indices_fuel(l->length(), l);
}

/// collatz_list n generates collatz sequence as a list.
std::shared_ptr<List<unsigned int>>
LoopifyNumbers::collatz_list_fuel(const unsigned int fuel,
                                  const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  struct _Call2 {
    const unsigned int _s0;
  };

  struct _Call3 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int n = _f.n;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int f = fuel - 1;
                if (n == 1u) {
                  _result = List<unsigned int>::ctor::Cons_(
                      1u, List<unsigned int>::ctor::Nil_());
                } else {
                  if ((n % 2u) == 0u) {
                    _stack.push_back(_Call1{n});
                    _stack.push_back(_Enter{Nat::div(n, 2u), std::move(f)});
                  } else {
                    if ((n % 3u) == 0u) {
                      _stack.push_back(_Call2{n});
                      _stack.push_back(_Enter{Nat::div(n, 3u), std::move(f)});
                    } else {
                      _stack.push_back(_Call3{n});
                      _stack.push_back(_Enter{((3u * n) + 1u), std::move(f)});
                    }
                  }
                }
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            },
            [&](_Call2 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            },
            [&](_Call3 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyNumbers::collatz_list(const unsigned int n) {
  return collatz_list_fuel(1000u, n);
}

/// sum_divisible_by k n sums all numbers from 1 to n divisible by k.
__attribute__((pure)) unsigned int
LoopifyNumbers::sum_divisible_by(const unsigned int k, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int m = n - 1;
                              if ((n % k) == 0u) {
                                _stack.push_back(_Call1{n});
                                _stack.push_back(_Enter{m});
                              } else {
                                _stack.push_back(_Enter{m});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  std::pair<unsigned int, unsigned int> _result;
  unsigned int _loop_u = u;
  unsigned int _loop_q = q;
  unsigned int _loop_x = x;
  bool _continue = true;
  while (_continue) {
    if (_loop_x <= 0) {
      {
        _result = std::make_pair(std::move(_loop_q), std::move(_loop_u));
        _continue = false;
      }
    } else {
      unsigned int x_ = _loop_x - 1;
      if (_loop_u <= 0) {
        {
          unsigned int _next_u = y;
          unsigned int _next_q = (_loop_q + 1);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_q = std::move(_next_q);
          _loop_x = std::move(_next_x);
          continue;
        }
      } else {
        unsigned int u_ = _loop_u - 1;
        {
          unsigned int _next_u = std::move(u_);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_x = std::move(_next_x);
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
