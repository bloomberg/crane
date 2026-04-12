#include <loopify_sequences.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// alternate_sum sign acc l alternating sum with sign flip.
__attribute__((pure)) unsigned int
LoopifySequences::alternate_sum(const unsigned int sign, const unsigned int acc,
                                const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  unsigned int _loop_sign = sign;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil &) {
                            _result = _loop_acc;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons &_args) {
                            unsigned int new_acc;
                            if (_loop_sign == 1u) {
                              new_acc = (_loop_acc + _args.d_a0);
                            } else {
                              new_acc = (((_loop_acc - _args.d_a0) > _loop_acc
                                              ? 0
                                              : (_loop_acc - _args.d_a0)));
                            }
                            unsigned int new_sign;
                            if (_loop_sign == 1u) {
                              new_sign = 0u;
                            } else {
                              new_sign = 1u;
                            }
                            std::shared_ptr<List<unsigned int>> _next_l =
                                _args.d_a1;
                            unsigned int _next_acc = new_acc;
                            unsigned int _next_sign = new_sign;
                            _loop_l = std::move(_next_l);
                            _loop_acc = std::move(_next_acc);
                            _loop_sign = std::move(_next_sign);
                          }},
               _loop_l->v());
  }
  return _result;
}

/// collatz_list n generates collatz sequence.
std::shared_ptr<List<unsigned int>>
LoopifySequences::collatz_list_fuel(const unsigned int fuel,
                                    const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  using _Frame = std::variant<_Enter>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                 const unsigned int n = _f.n;
                 const unsigned int fuel = _f.fuel;
                 if (fuel <= 0) {
                   _result = List<unsigned int>::nil();
                 } else {
                   unsigned int f = fuel - 1;
                   if (n == 1u) {
                     _result = List<unsigned int>::cons(
                         1u, List<unsigned int>::nil());
                   } else {
                     if ((2u ? n % 2u : n) == 0u) {
                       _stack.push_back(_Enter{(2u ? n / 2u : 0), f});
                     } else {
                       _stack.push_back(_Enter{((3u * n) + 1u), f});
                     }
                   }
                 }
               }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySequences::collatz_list(const unsigned int n) {
  return collatz_list_fuel(1000u, n);
}

/// run_sum l running sum (scanl for addition).
std::shared_ptr<List<unsigned int>>
LoopifySequences::run_sum_aux(const unsigned int acc,
                              const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              unsigned int new_acc = (_loop_acc + _args.d_a0);
              auto _cell = List<unsigned int>::cons(new_acc, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_acc = new_acc;
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySequences::run_sum(const std::shared_ptr<List<unsigned int>> &l) {
  return List<unsigned int>::cons(0u, run_sum_aux(0u, l));
}

/// rotate_left n l rotates list left by n positions.
std::shared_ptr<List<unsigned int>>
LoopifySequences::rotate_left_fuel(const unsigned int fuel,
                                   const unsigned int n,
                                   std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = std::move(_loop_l);
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        {
          _result = std::move(_loop_l);
          _continue = false;
        }
      } else {
        if (_loop_l.use_count() == 1 && _loop_l->v().index() == 0) {
          {
            _result = _loop_l;
            _continue = false;
          }
        } else {
          std::visit(
              Overloaded{[&](const typename List<unsigned int>::Nil &) {
                           _result = List<unsigned int>::nil();
                           _continue = false;
                         },
                         [&](const typename List<unsigned int>::Cons &_args) {
                           std::shared_ptr<List<unsigned int>> _next_l =
                               _args.d_a1->app(List<unsigned int>::cons(
                                   _args.d_a0, List<unsigned int>::nil()));
                           unsigned int _next_n = ((
                               (_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                           unsigned int _next_fuel = f;
                           _loop_l = std::move(_next_l);
                           _loop_n = std::move(_next_n);
                           _loop_fuel = std::move(_next_fuel);
                         }},
              _loop_l->v());
        }
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySequences::rotate_left(const unsigned int n,
                              const std::shared_ptr<List<unsigned int>> &l) {
  return rotate_left_fuel(100u, n, l);
}

/// sum_acc acc l sum with accumulator.
__attribute__((pure)) unsigned int
LoopifySequences::sum_acc(const unsigned int acc,
                          const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil &) {
                            _result = _loop_acc;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons &_args) {
                            std::shared_ptr<List<unsigned int>> _next_l =
                                _args.d_a1;
                            unsigned int _next_acc = (_loop_acc + _args.d_a0);
                            _loop_l = std::move(_next_l);
                            _loop_acc = std::move(_next_acc);
                          }},
               _loop_l->v());
  }
  return _result;
}

/// repeat_string s n repeats string n times (using list as string).
std::shared_ptr<List<unsigned int>>
LoopifySequences::repeat_string(const std::shared_ptr<List<unsigned int>> &s,
                                const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::nil();
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{s});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = _f._s0->app(_result); }},
               _frame);
  }
  return _result;
}

/// repeat_with_sep s sep n repeats with separator.
std::shared_ptr<List<unsigned int>> LoopifySequences::repeat_with_sep(
    std::shared_ptr<List<unsigned int>> s,
    const std::shared_ptr<List<unsigned int>> &sep, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::nil();
                            } else {
                              unsigned int m = n - 1;
                              if (m <= 0) {
                                _result = std::move(s);
                              } else {
                                unsigned int _x = m - 1;
                                _stack.push_back(_Call1{s, sep});
                                _stack.push_back(_Enter{m});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            _result = _f._s0->app(_f._s1->app(_result));
                          }},
               _frame);
  }
  return _result;
}

/// string_chain s n recursive string chain: s-chain(s, n-1)-end.
std::shared_ptr<List<unsigned int>> LoopifySequences::string_chain_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &s,
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<unsigned int>> &end_marker) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
    decltype(std::declval<const std::shared_ptr<List<unsigned int>> &>()->app(
        std::declval<const std::shared_ptr<List<unsigned int>> &>())) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                       _result = List<unsigned int>::nil();
                     } else {
                       unsigned int f = fuel - 1;
                       if (n <= 0u) {
                         _result = List<unsigned int>::nil();
                       } else {
                         _stack.push_back(_Call1{s, sep, sep->app(end_marker)});
                         _stack.push_back(
                             _Enter{(((n - 1u) > n ? 0 : (n - 1u))), f});
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     _result = _f._s0->app(_f._s1->app(_result->app(_f._s2)));
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifySequences::string_chain(
    const std::shared_ptr<List<unsigned int>> &s, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<unsigned int>> &end_marker) {
  return string_chain_fuel(1000u, s, n, sep, end_marker);
}

/// split_by_sign l base pos neg splits list based on base threshold.
__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifySequences::split_by_sign(const std::shared_ptr<List<unsigned int>> &l,
                                const unsigned int base,
                                std::shared_ptr<List<unsigned int>> pos,
                                std::shared_ptr<List<unsigned int>> neg) {
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result;
  std::shared_ptr<List<unsigned int>> _loop_neg = neg;
  std::shared_ptr<List<unsigned int>> _loop_pos = pos;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil &) {
                     _result = std::make_pair(std::move(_loop_pos),
                                              std::move(_loop_neg));
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons &_args) {
                     if (base <= _args.d_a0) {
                       std::shared_ptr<List<unsigned int>> _next_neg =
                           std::move(_loop_neg);
                       std::shared_ptr<List<unsigned int>> _next_pos =
                           List<unsigned int>::cons(_args.d_a0, _loop_pos);
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                       _loop_neg = std::move(_next_neg);
                       _loop_pos = std::move(_next_pos);
                       _loop_l = std::move(_next_l);
                     } else {
                       std::shared_ptr<List<unsigned int>> _next_neg =
                           List<unsigned int>::cons(_args.d_a0, _loop_neg);
                       std::shared_ptr<List<unsigned int>> _next_pos =
                           std::move(_loop_pos);
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                       _loop_neg = std::move(_next_neg);
                       _loop_pos = std::move(_next_pos);
                       _loop_l = std::move(_next_l);
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}

/// differences l computes differences between consecutive elements.
std::shared_ptr<List<unsigned int>>
LoopifySequences::differences(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<unsigned int>::nil();
                        } else {
                          _head = List<unsigned int>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        auto _cell = List<unsigned int>::cons(
                            (((_args0.d_a0 - _args.d_a0) > _args0.d_a0
                                  ? 0
                                  : (_args0.d_a0 - _args.d_a0))),
                            nullptr);
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// replace_at idx value l replaces element at index with value.
std::shared_ptr<List<unsigned int>>
LoopifySequences::replace_at(const unsigned int idx, const unsigned int value,
                             const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if (_loop_idx == 0u) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(value, _args.d_a1);
                } else {
                  _head = List<unsigned int>::cons(value, _args.d_a1);
                }
                _continue = false;
              } else {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_idx =
                    (((_loop_idx - 1u) > _loop_idx ? 0 : (_loop_idx - 1u)));
                _loop_l = std::move(_next_l);
                _loop_idx = std::move(_next_idx);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// cycle n l repeats list n times.
std::shared_ptr<List<unsigned int>>
LoopifySequences::cycle(const unsigned int n,
                        const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int n = _f.n;
              if (n <= 0) {
                _result = List<unsigned int>::nil();
              } else {
                unsigned int m = n - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result = List<unsigned int>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons &) -> void {
                          _stack.push_back(_Call1{l});
                          _stack.push_back(_Enter{m});
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

/// Helper: get first element.
__attribute__((pure)) unsigned int
LoopifySequences::first_elem(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil &) -> unsigned int {
                   return 0u;
                 },
                 [](const typename List<unsigned int>::Cons &_args)
                     -> unsigned int { return _args.d_a0; }},
      l->v());
}

/// Helper: get last element.
__attribute__((pure)) unsigned int
LoopifySequences::last_elem(const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil &) {
                     _result = 0u;
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons &_args) {
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil &) {
                               _result = _args.d_a0;
                               _continue = false;
                             },
                             [&](const typename List<unsigned int>::Cons &) {
                               _loop_l = _args.d_a1;
                             }},
                         _args.d_a1->v());
                   }},
        _loop_l->v());
  }
  return _result;
}

/// Helper: remove first element.
std::shared_ptr<List<unsigned int>>
LoopifySequences::tail_list(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil &)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [](const typename List<unsigned int>::Cons &_args)
              -> std::shared_ptr<List<unsigned int>> { return _args.d_a1; }},
      l->v());
}

/// Helper: remove last element.
std::shared_ptr<List<unsigned int>>
LoopifySequences::init_list(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil &) {
                               if (_last) {
                                 std::get<typename List<unsigned int>::Cons>(
                                     _last->v_mut())
                                     .d_a1 = List<unsigned int>::nil();
                               } else {
                                 _head = List<unsigned int>::nil();
                               }
                               _continue = false;
                             },
                             [&](const typename List<unsigned int>::Cons &) {
                               auto _cell = List<unsigned int>::cons(_args.d_a0,
                                                                     nullptr);
                               if (_last) {
                                 std::get<typename List<unsigned int>::Cons>(
                                     _last->v_mut())
                                     .d_a1 = _cell;
                               } else {
                                 _head = _cell;
                               }
                               _last = _cell;
                               _loop_l = _args.d_a1;
                             }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// is_palindrome s checks if list is a palindrome.
__attribute__((pure)) bool LoopifySequences::is_palindrome_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &s) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_s = s;
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
      unsigned int n = _loop_s->length();
      if (n <= 0) {
        {
          _result = true;
          _continue = false;
        }
      } else {
        unsigned int n0 = n - 1;
        if (n0 <= 0) {
          {
            _result = true;
            _continue = false;
          }
        } else {
          unsigned int _x = n0 - 1;
          if (first_elem(_loop_s) == last_elem(_loop_s)) {
            {
              std::shared_ptr<List<unsigned int>> _next_s =
                  init_list(tail_list(_loop_s));
              unsigned int _next_fuel = f;
              _loop_s = std::move(_next_s);
              _loop_fuel = std::move(_next_fuel);
            }
          } else {
            {
              _result = false;
              _continue = false;
            }
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySequences::is_palindrome(const std::shared_ptr<List<unsigned int>> &s) {
  return is_palindrome_fuel(1000u, s);
}

/// string_subsequences s generates all subsequences treating list as string.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySequences::string_subsequences(
    const std::shared_ptr<List<unsigned int>> &s) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> s;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{s});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> s = _f.s;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::nil(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    nil());
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  s->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  sub_rest = _result;
              std::function<std::shared_ptr<
                  List<std::shared_ptr<List<unsigned int>>>>(
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
                  map_prepend_c;
              map_prepend_c =
                  [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                          lsts)
                  -> std::shared_ptr<
                      List<std::shared_ptr<List<unsigned int>>>> {
                struct _Enter {
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                      lsts;
                };
                struct _Call1 {
                  decltype(List<unsigned int>::cons(
                      _args.d_a0,
                      std::declval<const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &>()
                          .d_a0)) _s0;
                };
                using _Frame = std::variant<_Enter, _Call1>;
                std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                    _result{};
                std::vector<_Frame> _stack;
                _stack.push_back(_Enter{lsts});
                while (!_stack.empty()) {
                  _Frame _frame = std::move(_stack.back());
                  _stack.pop_back();
                  std::visit(
                      Overloaded{
                          [&](_Enter _f) {
                            std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>>
                                lsts = _f.lsts;
                            std::visit(
                                Overloaded{
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Nil &)
                                        -> void {
                                      _result = List<std::shared_ptr<
                                          List<unsigned int>>>::nil();
                                    },
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Cons &_args0)
                                        -> void {
                                      _stack.push_back(
                                          _Call1{List<unsigned int>::cons(
                                              _args.d_a0, _args0.d_a0)});
                                      _stack.push_back(_Enter{_args0.d_a1});
                                    }},
                                lsts->v());
                          },
                          [&](_Call1 _f) {
                            _result =
                                List<std::shared_ptr<List<unsigned int>>>::cons(
                                    _f._s0, _result);
                          }},
                      _frame);
                }
                return _result;
              };
              _result = sub_rest->app(map_prepend_c(sub_rest));
            }},
        _frame);
  }
  return _result;
}

/// run_length_groups l groups consecutive runs into sublist lengths.
std::shared_ptr<List<unsigned int>> LoopifySequences::run_length_groups_aux(
    const unsigned int prev, const unsigned int count,
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_count = count;
  unsigned int _loop_prev = prev;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_loop_count == 0u) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              } else {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(
                      _loop_count, List<unsigned int>::nil());
                } else {
                  _head = List<unsigned int>::cons(_loop_count,
                                                   List<unsigned int>::nil());
                }
                _continue = false;
              }
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if (_loop_prev == _args.d_a0) {
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_count = (_loop_count + 1);
                unsigned int _next_prev = _args.d_a0;
                _loop_l = std::move(_next_l);
                _loop_count = std::move(_next_count);
                _loop_prev = std::move(_next_prev);
              } else {
                if (_loop_count == 0u) {
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_count = 1u;
                  unsigned int _next_prev = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_count = std::move(_next_count);
                  _loop_prev = std::move(_next_prev);
                } else {
                  auto _cell = List<unsigned int>::cons(_loop_count, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_count = 1u;
                  unsigned int _next_prev = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_count = std::move(_next_count);
                  _loop_prev = std::move(_next_prev);
                }
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifySequences::run_length_groups(
    const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil &)
                     -> std::shared_ptr<List<unsigned int>> {
                   return List<unsigned int>::nil();
                 },
                 [](const typename List<unsigned int>::Cons &_args)
                     -> std::shared_ptr<List<unsigned int>> {
                   return run_length_groups_aux(_args.d_a0, 1u, _args.d_a1);
                 }},
      l->v());
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool
LoopifySequences::is_prefix_of(const std::shared_ptr<List<unsigned int>> &l1,
                               const std::shared_ptr<List<unsigned int>> &l2) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        _result = false;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          std::shared_ptr<List<unsigned int>> _next_l2 =
                              _args0.d_a1;
                          std::shared_ptr<List<unsigned int>> _next_l1 =
                              _args.d_a1;
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        } else {
                          _result = false;
                          _continue = false;
                        }
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _result;
}

/// lis l longest increasing subsequence (greedy, not optimal).
std::shared_ptr<List<unsigned int>>
LoopifySequences::lis(std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (_loop_l.use_count() == 1 && _loop_l->v().index() == 0) {
      {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _loop_l;
        } else {
          _head = _loop_l;
        }
        _continue = false;
      }
    } else {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) {
                          if (_last) {
                            std::get<typename List<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = std::move(_loop_l);
                          } else {
                            _head = std::move(_loop_l);
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons &_args0) {
                          if (_args.d_a0 < _args0.d_a0) {
                            auto _cell =
                                List<unsigned int>::cons(_args.d_a0, nullptr);
                            if (_last) {
                              std::get<typename List<unsigned int>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            _loop_l = _args.d_a1;
                          } else {
                            _loop_l = _args.d_a1;
                          }
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
  }
  return _head;
}

/// Helper: check if element is in list.
__attribute__((pure)) bool
LoopifySequences::elem(const unsigned int x,
                       const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const unsigned int &>() ==
             std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil &)
                                 -> void { _result = false; },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
                               _stack.push_back(_Call1{x == _args.d_a0});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 || _result); }},
        _frame);
  }
  return _result;
}

/// Helper: filter list.
std::shared_ptr<List<unsigned int>>
LoopifySequences::filter_ne(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if (x == _args.d_a0) {
                _loop_l = _args.d_a1;
              } else {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// nub l removes duplicates from list.
std::shared_ptr<List<unsigned int>>
LoopifySequences::nub_fuel(const unsigned int fuel,
                           const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &_args) {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l =
                    filter_ne(_args.d_a0, _args.d_a1);
                unsigned int _next_fuel = f;
                _loop_l = std::move(_next_l);
                _loop_fuel = std::move(_next_fuel);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySequences::nub(const std::shared_ptr<List<unsigned int>> &l) {
  return nub_fuel(l->length(), l);
}

/// group l groups consecutive equal elements.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySequences::group_fuel(const unsigned int fuel,
                             const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  struct _Call2 {
    decltype(List<unsigned int>::cons(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        List<unsigned int>::nil())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
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
                _result = List<std::shared_ptr<List<unsigned int>>>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result =
                              List<std::shared_ptr<List<unsigned int>>>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons &_args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil &)
                                      -> void {
                                    _result = List<
                                        std::shared_ptr<List<unsigned int>>>::
                                        cons(List<unsigned int>::cons(
                                                 _args.d_a0,
                                                 List<unsigned int>::nil()),
                                             List<std::shared_ptr<
                                                 List<unsigned int>>>::nil());
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          &_args0) -> void {
                                    if (_args.d_a0 == _args0.d_a0) {
                                      _stack.push_back(_Call1{_args});
                                      _stack.push_back(_Enter{_args.d_a1, f});
                                    } else {
                                      _stack.push_back(
                                          _Call2{List<unsigned int>::cons(
                                              _args.d_a0,
                                              List<unsigned int>::nil())});
                                      _stack.push_back(_Enter{_args.d_a1, f});
                                    }
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil &) -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::cons(
                                    _args.d_a0, List<unsigned int>::nil()),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    nil());
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args1)
                          -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::cons(_args.d_a0,
                                                         _args1.d_a0),
                                _args1.d_a1);
                      }},
                  _result->v());
            },
            [&](_Call2 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::cons(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifySequences::group(const std::shared_ptr<List<unsigned int>> &l) {
  return group_fuel(l->length(), l);
}

/// Helper: get head with default.
__attribute__((pure)) unsigned int
LoopifySequences::head_or(const unsigned int default0,
                          const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::Nil &) -> unsigned int {
                   return default0;
                 },
                 [](const typename List<unsigned int>::Cons &_args)
                     -> unsigned int { return _args.d_a0; }},
      l->v());
}

/// remove_if_sum_even l removes elements where sum with next is even.
std::shared_ptr<List<unsigned int>> LoopifySequences::remove_if_sum_even(
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              unsigned int next = head_or(0u, _args.d_a1);
              if ((2u ? (_args.d_a0 + next) % 2u : (_args.d_a0 + next)) == 0u) {
                _loop_l = _args.d_a1;
              } else {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifySequences::run_length_encode_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
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
                _result = List<std::pair<unsigned int, unsigned int>>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result = List<
                              std::pair<unsigned int, unsigned int>>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons &_args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil &)
                                      -> void {
                                    _result = List<
                                        std::pair<unsigned int, unsigned int>>::
                                        cons(std::make_pair(_args.d_a0, 1u),
                                             List<std::pair<unsigned int,
                                                            unsigned int>>::
                                                 nil());
                                  },
                                  [&](const typename List<unsigned int>::Cons &)
                                      -> void {
                                    _stack.push_back(_Call1{_args});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Nil &)
                          -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::cons(
                                std::make_pair(_args.d_a0, 1u),
                                List<std::pair<unsigned int,
                                               unsigned int>>::nil());
                      },
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Cons &_args1)
                          -> void {
                        const unsigned int &y = _args1.d_a0.first;
                        const unsigned int &n = _args1.d_a0.second;
                        if (_args.d_a0 == y) {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(y, (n + 1)), _args1.d_a1);
                        } else {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(_args.d_a0, 1u),
                                  List<std::pair<unsigned int, unsigned int>>::
                                      cons(std::make_pair(y, n), _args1.d_a1));
                        }
                      }},
                  _result->v());
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifySequences::run_length_encode(
    const std::shared_ptr<List<unsigned int>> &l) {
  return run_length_encode_fuel(l->length(), l);
}

/// between lo hi l filters elements in range lo, hi.
std::shared_ptr<List<unsigned int>>
LoopifySequences::between(const unsigned int lo, const unsigned int hi,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if ((lo <= _args.d_a0 && _args.d_a0 <= hi)) {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}
