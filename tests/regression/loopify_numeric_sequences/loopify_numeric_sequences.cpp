#include <loopify_numeric_sequences.h>

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
LoopifyNumericSequences::collatz_length_fuel(const unsigned int fuel,
                                             const unsigned int n) {
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
                       unsigned int fuel_ = fuel - 1;
                       if (n <= 1u) {
                         _result = 0u;
                       } else {
                         if ((n % 2u) == 0u) {
                           _stack.push_back(_Call1{1u});
                           _stack.push_back(_Enter{Nat::div(n, 2u), fuel_});
                         } else {
                           _stack.push_back(_Call2{1u});
                           _stack.push_back(_Enter{((3u * n) + 1u), fuel_});
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); },
                   [&](_Call2 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::collatz_length(const unsigned int n) {
  return collatz_length_fuel((n * 100u), n);
}

std::shared_ptr<List<unsigned int>>
LoopifyNumericSequences::collatz_sequence_fuel(const unsigned int fuel,
                                               const unsigned int n) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::ctor::Nil_();
        } else {
          _head = List<unsigned int>::ctor::Nil_();
        }
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 1u) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::ctor::Cons_(
                    1u, List<unsigned int>::ctor::Nil_());
          } else {
            _head = List<unsigned int>::ctor::Cons_(
                1u, List<unsigned int>::ctor::Nil_());
          }
          _continue = false;
        }
      } else {
        if ((_loop_n % 2u) == 0u) {
          {
            auto _cell = List<unsigned int>::ctor::Cons_(_loop_n, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            unsigned int _next_n = Nat::div(_loop_n, 2u);
            unsigned int _next_fuel = std::move(fuel_);
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        } else {
          {
            auto _cell = List<unsigned int>::ctor::Cons_(_loop_n, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            unsigned int _next_n = ((3u * _loop_n) + 1u);
            unsigned int _next_fuel = std::move(fuel_);
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyNumericSequences::collatz_sequence(const unsigned int n) {
  return collatz_sequence_fuel((n * 100u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::tribonacci_fuel(const unsigned int fuel,
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
                             _stack.push_back(_Call1{
                                 (((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                 (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                             _stack.push_back(_Enter{
                                 (((n - 3u) > n ? 0 : (n - 3u))), fuel_});
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
                   [&](_Call3 _f) { _result = ((_result + _f._s1) + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::tribonacci(const unsigned int n) {
  return tribonacci_fuel((n * 3u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::staircase_fuel(const unsigned int fuel,
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
                       unsigned int fuel_ = fuel - 1;
                       if (n <= 0u) {
                         _result = 1u;
                       } else {
                         if (n == 1u) {
                           _result = 1u;
                         } else {
                           _stack.push_back(
                               _Call1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                      (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                           _stack.push_back(
                               _Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
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
                   [&](_Call3 _f) { _result = ((_result + _f._s1) + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::staircase(const unsigned int n) {
  return staircase_fuel((n * 3u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::digitsum_fuel(const unsigned int fuel,
                                       const unsigned int n) {
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
                              unsigned int fuel_ = fuel - 1;
                              if (n <= 0u) {
                                _result = 0u;
                              } else {
                                _stack.push_back(_Call1{(n % 10u)});
                                _stack.push_back(
                                    _Enter{Nat::div(n, 10u), fuel_});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::digitsum(const unsigned int n) {
  return digitsum_fuel((n + 1u), n);
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::dec_to_bin_fuel(const unsigned int fuel,
                                         const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((std::declval<const unsigned int &>() % 2u)) _s0;
    decltype(10u) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
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
                       unsigned int fuel_ = fuel - 1;
                       if (n <= 0u) {
                         _result = 0u;
                       } else {
                         _stack.push_back(_Call1{(n % 2u), 10u});
                         _stack.push_back(_Enter{Nat::div(n, 2u), fuel_});
                       }
                     }
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + (_f._s1 * _result)); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::dec_to_bin(const unsigned int n) {
  return dec_to_bin_fuel((n + 1u), n);
}

__attribute__((pure)) unsigned int LoopifyNumericSequences::alternate_sum(
    const bool sign, const unsigned int acc,
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _loop_sign = sign;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = std::move(_loop_acc);
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (_loop_sign) {
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_acc = (std::move(_loop_acc) + _args.d_a0);
                bool _next_sign = false;
                _loop_l = std::move(_next_l);
                _loop_acc = std::move(_next_acc);
                _loop_sign = std::move(_next_sign);
              } else {
                if (_args.d_a0 <= _loop_acc) {
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_acc = ((
                      (std::move(_loop_acc) - _args.d_a0) > std::move(_loop_acc)
                          ? 0
                          : (std::move(_loop_acc) - _args.d_a0)));
                  bool _next_sign = true;
                  _loop_l = std::move(_next_l);
                  _loop_acc = std::move(_next_acc);
                  _loop_sign = std::move(_next_sign);
                } else {
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_acc = 0u;
                  bool _next_sign = true;
                  _loop_l = std::move(_next_l);
                  _loop_acc = std::move(_next_acc);
                  _loop_sign = std::move(_next_sign);
                }
              }
            }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::sum_divisors_aux(const unsigned int n,
                                          const unsigned int d) {
  struct _Enter {
    const unsigned int d;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{d});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int d = _f.d;
                            if (d <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int d_ = d - 1;
                              if ((n % d) == 0u) {
                                _stack.push_back(_Call1{d});
                                _stack.push_back(_Enter{d_});
                              } else {
                                _stack.push_back(_Enter{d_});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericSequences::sum_divisors(const unsigned int n) {
  if (n <= 1u) {
    return 0u;
  } else {
    return sum_divisors_aux(n, (((n - 1u) > n ? 0 : (n - 1u))));
  }
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
