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

__attribute__((pure)) unsigned int
LoopifyNumbers::factorial(const unsigned int n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            unsigned int n = _f.n;
                            if (n <= 0) {
                              {
                                _result = 1u;
                              }
                            } else {
                              unsigned int m = n - 1;
                              {
                                _stack.push_back(_Call1{n});
                                _stack.push_back(_Enter{m});
                              }
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
                            unsigned int n = _f.n;
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
    unsigned int n;
    unsigned int fuel;
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
                     unsigned int n = _f.n;
                     unsigned int fuel = _f.fuel;
                     if (fuel <= 0) {
                       {
                         _result = 0u;
                       }
                     } else {
                       unsigned int f = fuel - 1;
                       if (n <= 0) {
                         {
                           _result = 0u;
                         }
                       } else {
                         unsigned int n0 = n - 1;
                         if (n0 <= 0) {
                           {
                             _result = 0u;
                           }
                         } else {
                           unsigned int n1 = n0 - 1;
                           if (n1 <= 0) {
                             {
                               _result = 1u;
                             }
                           } else {
                             unsigned int m = n1 - 1;
                             {
                               _stack.push_back(
                                   _Call1{(m + 1), f, ((m + 1) + 1), f});
                               _stack.push_back(_Enter{m, f});
                             }
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
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 100u;
  if (_inl_fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n <= 0) {
      return 0u;
    } else {
      unsigned int n0 = _inl_n - 1;
      if (n0 <= 0) {
        return 0u;
      } else {
        unsigned int n1 = n0 - 1;
        if (n1 <= 0) {
          return 1u;
        } else {
          unsigned int m = n1 - 1;
          return (tribonacci_fuel(f, ((m + 1) + 1)) +
                  (tribonacci_fuel(f, (m + 1)) + tribonacci_fuel(f, m)));
        }
      }
    }
  }
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
  const unsigned int _inl_b = b;
  const unsigned int _inl_a = a;
  const unsigned int _inl_fuel = (a + b);
  if (_inl_fuel <= 0) {
    return std::move(_inl_a);
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_b <= 0) {
      return _inl_a;
    } else {
      unsigned int _x = _inl_b - 1;
      return gcd_fuel(std::move(f), _inl_b, (_inl_a % _inl_b));
    }
  }
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
                            unsigned int k = _f.k;
                            unsigned int n = _f.n;
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
                            unsigned int col = _f.col;
                            unsigned int row = _f.row;
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
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_m = m;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = 0u;
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_m <= 0) {
        {
          _result = (_loop_n + 1);
          _continue = false;
        }
      } else {
        unsigned int m_ = _loop_m - 1;
        if (_loop_n <= 0) {
          {
            unsigned int _next_n = 1u;
            unsigned int _next_m = std::move(m_);
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_m = std::move(_next_m);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        } else {
          unsigned int n_ = _loop_n - 1;
          {
            unsigned int _next_n = ackermann_fuel(f, _loop_m, std::move(n_));
            unsigned int _next_m = m_;
            unsigned int _next_fuel = f;
            _loop_n = std::move(_next_n);
            _loop_m = std::move(_next_m);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyNumbers::ack(const unsigned int m,
                                                       const unsigned int n) {
  const unsigned int _inl_n = n;
  const unsigned int _inl_m = m;
  const unsigned int _inl_fuel = 1000u;
  if (_inl_fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_m <= 0) {
      return (_inl_n + 1);
    } else {
      unsigned int m_ = _inl_m - 1;
      if (_inl_n <= 0) {
        return ackermann_fuel(f, std::move(m_), 1u);
      } else {
        unsigned int n_ = _inl_n - 1;
        return ackermann_fuel(f, m_, ackermann_fuel(f, _inl_m, std::move(n_)));
      }
    }
  }
}

__attribute__((pure)) unsigned int
LoopifyNumbers::collatz_length_fuel(const unsigned int fuel,
                                    const unsigned int n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
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
                            unsigned int n = _f.n;
                            unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              {
                                _result = 0u;
                              }
                            } else {
                              unsigned int f = fuel - 1;
                              if (n == 1u) {
                                {
                                  _result = 0u;
                                }
                              } else {
                                if ((n % 2u) == 0u) {
                                  {
                                    _stack.push_back(_Call1{});
                                    _stack.push_back(
                                        _Enter{Nat::div(n, 2u), std::move(f)});
                                  }
                                } else {
                                  {
                                    _stack.push_back(_Call2{});
                                    _stack.push_back(
                                        _Enter{((3u * n) + 1u), std::move(f)});
                                  }
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
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 1000u;
  if (_inl_fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n == 1u) {
      return 0u;
    } else {
      if ((_inl_n % 2u) == 0u) {
        return (collatz_length_fuel(std::move(f), Nat::div(_inl_n, 2u)) + 1);
      } else {
        return (collatz_length_fuel(std::move(f), ((3u * _inl_n) + 1u)) + 1);
      }
    }
  }
}

__attribute__((pure)) unsigned int
LoopifyNumbers::digitsum_fuel(const unsigned int fuel, const unsigned int n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  struct _Call1 {
    decltype((n % 10u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            unsigned int n = _f.n;
                            unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              {
                                _result = 0u;
                              }
                            } else {
                              unsigned int f = fuel - 1;
                              if (n <= 0) {
                                {
                                  _result = 0u;
                                }
                              } else {
                                unsigned int _x = n - 1;
                                {
                                  _stack.push_back(_Call1{(n % 10u)});
                                  _stack.push_back(_Enter{Nat::div(n, 10u), f});
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
LoopifyNumbers::digitsum(const unsigned int n) {
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 100u;
  if (_inl_fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n <= 0) {
      return 0u;
    } else {
      unsigned int _x = _inl_n - 1;
      return ((_inl_n % 10u) + digitsum_fuel(f, Nat::div(_inl_n, 10u)));
    }
  }
}

__attribute__((pure)) unsigned int
LoopifyNumbers::dec_to_bin_fuel(const unsigned int fuel, const unsigned int n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  using _Frame = std::variant<_Enter>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                 unsigned int n = _f.n;
                 unsigned int fuel = _f.fuel;
                 if (fuel <= 0) {
                   {
                     _result = 0u;
                   }
                 } else {
                   unsigned int f = fuel - 1;
                   if (n <= 0) {
                     {
                       _result = 0u;
                     }
                   } else {
                     unsigned int _x = n - 1;
                     unsigned int digit = (n % 2u);
                     unsigned int rest =
                         dec_to_bin_fuel(f, [](const unsigned int _inl_x,
                                               const unsigned int _inl_y) {
                           if (_inl_y <= 0) {
                             return std::move(_inl_y);
                           } else {
                             unsigned int y_ = _inl_y - 1;
                             return Nat::divmod(_inl_x, y_, 0u, y_).first;
                           }
                         }(n, 2u));
                     {
                       _result = (std::move(digit) + (10u * std::move(rest)));
                     }
                   }
                 }
               }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::dec_to_bin(const unsigned int n) {
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 100u;
  if (_inl_fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n <= 0) {
      return 0u;
    } else {
      unsigned int _x = _inl_n - 1;
      unsigned int digit = (_inl_n % 2u);
      unsigned int rest = dec_to_bin_fuel(f, Nat::div(_inl_n, 2u));
      return (std::move(digit) + (10u * std::move(rest)));
    }
  }
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_to(const unsigned int n) {
  struct _Enter {
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            unsigned int n = _f.n;
                            if (n <= 0) {
                              {
                                _result = 0u;
                              }
                            } else {
                              unsigned int m = n - 1;
                              {
                                _stack.push_back(_Call1{n});
                                _stack.push_back(_Enter{m});
                              }
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
    unsigned int n;
  };

  struct _Call1 {
    decltype((n * n)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            unsigned int n = _f.n;
                            if (n <= 0) {
                              {
                                _result = 0u;
                              }
                            } else {
                              unsigned int m = n - 1;
                              {
                                _stack.push_back(_Call1{(n * n)});
                                _stack.push_back(_Enter{m});
                              }
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
    unsigned int n;
    unsigned int fuel;
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
                     unsigned int n = _f.n;
                     unsigned int fuel = _f.fuel;
                     if (fuel <= 0) {
                       {
                         _result = 0u;
                       }
                     } else {
                       unsigned int f = fuel - 1;
                       if (n <= 0) {
                         {
                           _result = 1u;
                         }
                       } else {
                         unsigned int n0 = n - 1;
                         if (n0 <= 0) {
                           {
                             _result = 1u;
                           }
                         } else {
                           unsigned int n1 = n0 - 1;
                           if (n1 <= 0) {
                             {
                               _result = 2u;
                             }
                           } else {
                             unsigned int m = n1 - 1;
                             {
                               _stack.push_back(
                                   _Call1{(m + 1), f, ((m + 1) + 1), f});
                               _stack.push_back(_Enter{m, f});
                             }
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
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 100u;
  if (_inl_fuel <= 0) {
    return 0u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n <= 0) {
      return 1u;
    } else {
      unsigned int n0 = _inl_n - 1;
      if (n0 <= 0) {
        return 1u;
      } else {
        unsigned int n1 = n0 - 1;
        if (n1 <= 0) {
          return 2u;
        } else {
          unsigned int m = n1 - 1;
          return (staircase_fuel(f, ((m + 1) + 1)) +
                  (staircase_fuel(f, (m + 1)) + staircase_fuel(f, m)));
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int
LoopifyNumbers::multi_guard(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s0;
  };

  struct _Call2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> unsigned int {
                               _result = 0u;
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> unsigned int {
                               if (10u < _args.d_a0) {
                                 _stack.push_back(_Call1{_args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               } else {
                                 if (0u < _args.d_a0) {
                                   _stack.push_back(_Enter{_args.d_a1});
                                 } else {
                                   _stack.push_back(_Call2{1u});
                                   _stack.push_back(_Enter{_args.d_a1});
                                 }
                               }
                               return {};
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); },
                   [&](_Call2 _f) { _result = (_result + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyNumbers::is_even(const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = true;
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      const unsigned int _inl_n = m;
      if (_inl_n <= 0) {
        {
          _result = false;
          _continue = false;
        }
      } else {
        unsigned int m = _inl_n - 1;
        {
          _loop_n = m;
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool LoopifyNumbers::is_odd(const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = false;
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      const unsigned int _inl_n = m;
      if (_inl_n <= 0) {
        {
          _result = true;
          _continue = false;
        }
      } else {
        unsigned int m = _inl_n - 1;
        {
          _loop_n = m;
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_odd_indices(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::Cons _args) -> unsigned int {
            return (_args.d_a0 + sum_even_indices(_args.d_a1));
          }},
      l->v());
}

__attribute__((pure)) unsigned int
LoopifyNumbers::sum_even_indices(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::Cons _args) -> unsigned int {
            return sum_odd_indices(_args.d_a1);
          }},
      l->v());
}

__attribute__((pure)) unsigned int
LoopifyNumbers::nest_apply_fuel(const unsigned int fuel, const unsigned int n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  using _Frame = std::variant<_Enter>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                 unsigned int n = _f.n;
                 unsigned int fuel = _f.fuel;
                 if (fuel <= 0) {
                   {
                     _result = 1u;
                   }
                 } else {
                   unsigned int f = fuel - 1;
                   if (n <= 0) {
                     {
                       _result = 1u;
                     }
                   } else {
                     unsigned int m = n - 1;
                     unsigned int r = nest_apply_fuel(f, m);
                     if (r <= 0) {
                       {
                         _result = 1u;
                       }
                     } else {
                       unsigned int k = r - 1;
                       _stack.push_back(_Enter{std::move(k), f});
                     }
                   }
                 }
               }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumbers::nest_apply(const unsigned int n) {
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 1000u;
  if (_inl_fuel <= 0) {
    return 1u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n <= 0) {
      return 1u;
    } else {
      unsigned int m = _inl_n - 1;
      unsigned int r = nest_apply_fuel(f, m);
      if (r <= 0) {
        return 1u;
      } else {
        unsigned int k = r - 1;
        return nest_apply_fuel(f, std::move(k));
      }
    }
  }
}

__attribute__((pure)) unsigned int
LoopifyNumbers::mixed_arith_fuel(const unsigned int fuel,
                                 const unsigned int n) {
  struct _Enter {
    unsigned int n;
    unsigned int fuel;
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
                     unsigned int n = _f.n;
                     unsigned int fuel = _f.fuel;
                     if (fuel <= 0) {
                       {
                         _result = 1u;
                       }
                     } else {
                       unsigned int f = fuel - 1;
                       if (n <= 0) {
                         {
                           _result = 1u;
                         }
                       } else {
                         unsigned int m = n - 1;
                         if (m <= 0) {
                           {
                             _result = 1u;
                           }
                         } else {
                           unsigned int n0 = m - 1;
                           if (n0 <= 0) {
                             {
                               _result = 1u;
                             }
                           } else {
                             unsigned int _x = n0 - 1;
                             {
                               _stack.push_back(_Call1{
                                   (((n - 2u) > n ? 0 : (n - 2u))), f, m, f});
                               _stack.push_back(
                                   _Enter{(((n - 3u) > n ? 0 : (n - 3u))), f});
                             }
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
  const unsigned int _inl_n = n;
  const unsigned int _inl_fuel = 1000u;
  if (_inl_fuel <= 0) {
    return 1u;
  } else {
    unsigned int f = _inl_fuel - 1;
    if (_inl_n <= 0) {
      return 1u;
    } else {
      unsigned int m = _inl_n - 1;
      if (m <= 0) {
        return 1u;
      } else {
        unsigned int n0 = m - 1;
        if (n0 <= 0) {
          return 1u;
        } else {
          unsigned int _x = n0 - 1;
          return ((mixed_arith_fuel(f, m) *
                   mixed_arith_fuel(
                       f, (((_inl_n - 2u) > _inl_n ? 0 : (_inl_n - 2u))))) +
                  mixed_arith_fuel(
                      f, (((_inl_n - 3u) > _inl_n ? 0 : (_inl_n - 3u)))));
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int LoopifyNumbers::power(const unsigned int b,
                                                         const unsigned int e) {
  struct _Enter {
    unsigned int e;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            unsigned int e = _f.e;
                            if (e <= 0) {
                              {
                                _result = 1u;
                              }
                            } else {
                              unsigned int e_ = e - 1;
                              {
                                _stack.push_back(_Call1{b});
                                _stack.push_back(_Enter{e_});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 * _result); }},
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
