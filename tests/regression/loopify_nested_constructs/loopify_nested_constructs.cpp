#include <loopify_nested_constructs.h>

#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::multi_let(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
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
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int n_ = n - 1;
                              unsigned int b = (n_ * 2u);
                              unsigned int c = (std::move(b) + 3u);
                              _stack.push_back(_Call1{std::move(c)});
                              _stack.push_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::nested_if_fuel(const unsigned int fuel,
                                        const unsigned int n) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = 0u;
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        {
          _result = 0u;
          _continue = false;
        }
      } else {
        if (_loop_n == 1u) {
          {
            _result = 1u;
            _continue = false;
          }
        } else {
          if ((2u ? _loop_n % 2u : _loop_n) == 0u) {
            if (10u < _loop_n) {
              {
                unsigned int _next_n = (2u ? _loop_n / 2u : 0);
                unsigned int _next_fuel = fuel_;
                _loop_n = std::move(_next_n);
                _loop_fuel = std::move(_next_fuel);
                continue;
              }
            } else {
              {
                unsigned int _next_n =
                    (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                unsigned int _next_fuel = fuel_;
                _loop_n = std::move(_next_n);
                _loop_fuel = std::move(_next_fuel);
                continue;
              }
            }
          } else {
            {
              unsigned int _next_n =
                  (((_loop_n - 2u) > _loop_n ? 0 : (_loop_n - 2u)));
              unsigned int _next_fuel = fuel_;
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

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::nested_if(const unsigned int n) {
  return nested_if_fuel(n, n);
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::deep_nest(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {};

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
                              unsigned int n_ = n - 1;
                              _stack.push_back(_Call1{});
                              _stack.push_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) {
                            unsigned int inner = _result;
                            unsigned int mid = (std::move(inner) + 1u);
                            _result = (std::move(mid) * 2u);
                          }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::let_nested(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
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
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int n_ = n - 1;
                              unsigned int a = (n_ + 1u);
                              _stack.push_back(_Call1{std::move(a)});
                              _stack.push_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::mod_pattern_fuel(const unsigned int fuel,
                                          const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
    decltype(1u) _s1;
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
                              _result = 1u;
                            } else {
                              unsigned int fuel_ = fuel - 1;
                              if (n <= 1u) {
                                _result = 1u;
                              } else {
                                _stack.push_back(_Call1{n, 1u});
                                _stack.push_back(_Enter{
                                    (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            _result = ((_f._s1 + _result)
                                           ? _f._s0 % (_f._s1 + _result)
                                           : _f._s0);
                          }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::mod_pattern(const unsigned int n) {
  return mod_pattern_fuel(n, n);
}

__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyNestedConstructs::tuple_constr(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const unsigned int n = _f.n;
                     if (n <= 0) {
                       _result = std::make_pair(std::make_pair(0u, 0u), 0u);
                     } else {
                       unsigned int n_ = n - 1;
                       _stack.push_back(_Call1{n});
                       _stack.push_back(_Enter{n_});
                     }
                   },
                   [&](_Call1 _f) {
                     const unsigned int n = _f._s0;
                     std::pair<unsigned int, unsigned int> p = _result.first;
                     unsigned int c = _result.second;
                     unsigned int a = p.first;
                     unsigned int b = p.second;
                     _result = std::make_pair(std::make_pair((a + 1u), (b + n)),
                                              (c + (n * n)));
                   }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::alternating_ops(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  struct _Call2 {
    decltype((std::declval<const unsigned int &>() * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
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
                              if ((2u ? n % 2u : n) == 0u) {
                                _stack.push_back(_Call1{n});
                                _stack.push_back(_Enter{n_});
                              } else {
                                _stack.push_back(_Call2{(n * 2u)});
                                _stack.push_back(_Enter{n_});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); },
                          [&](_Call2 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyNestedConstructs::chained_comp_fuel(const unsigned int fuel,
                                           const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
  };

  struct _Combine {
    bool _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  bool _result{};
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
                       _result = true;
                     } else {
                       unsigned int fuel_ = fuel - 1;
                       if (n <= 2u) {
                         _result = true;
                       } else {
                         _stack.push_back(
                             _After{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                         _stack.push_back(
                             _Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
                       }
                     }
                   },
                   [&](_After _f) {
                     _stack.push_back(_Combine{_result});
                     _stack.push_back(_Enter{_f._a0, _f._a1});
                   },
                   [&](_Combine _f) { _result = (_result && _f._left); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::chained_comp(const unsigned int n) {
  if (chained_comp_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::compute_with_lets(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
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
                                unsigned int n__ = n_ - 1;
                                _stack.push_back(_Call1{n__});
                                _stack.push_back(_Enter{n_});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            unsigned int n__ = _f._s0;
                            unsigned int x = _result;
                            _stack.push_back(_Call2{x});
                            _stack.push_back(_Enter{n__});
                          },
                          [&](_Call2 _f) {
                            unsigned int x = _f._s0;
                            unsigned int y = _result;
                            unsigned int z = (std::move(x) + std::move(y));
                            _result = (std::move(z) * 2u);
                          }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNestedConstructs::nested_match(const unsigned int n) {
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
                              unsigned int n_ = n - 1;
                              if (n_ <= 0) {
                                _result = 1u;
                              } else {
                                unsigned int n__ = n_ - 1;
                                _stack.push_back(_Call1{n});
                                _stack.push_back(_Enter{n__});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}
