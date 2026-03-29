#include <loopify_strings.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoopifyStrings::append(const std::shared_ptr<List<unsigned int>> &l1,
                       std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(_loop_l2);
              } else {
                _head = std::move(_loop_l2);
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l2 =
                  std::move(_loop_l2);
              std::shared_ptr<List<unsigned int>> _next_l1 = _args.d_a1;
              _loop_l2 = std::move(_next_l2);
              _loop_l1 = std::move(_next_l1);
            }},
        _loop_l1->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::join_with(const unsigned int sep,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        } else {
                          _head = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args.d_a0, nullptr);
                        auto _cell1 = List<unsigned int>::cons(sep, nullptr);
                        std::get<typename List<unsigned int>::Cons>(
                            _cell->v_mut())
                            .d_a1 = _cell1;
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell1;
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::repeat_string(const std::shared_ptr<List<unsigned int>> &s,
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
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const unsigned int n = _f.n;
                     if (n <= 0) {
                       _result = List<unsigned int>::nil();
                     } else {
                       unsigned int n_ = n - 1;
                       _stack.push_back(_Call1{s});
                       _stack.push_back(_Enter{n_});
                     }
                   },
                   [&](_Call1 _f) { _result = append(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::repeat_with_sep(std::shared_ptr<List<unsigned int>> s,
                                const std::shared_ptr<List<unsigned int>> &sep,
                                const unsigned int n) {
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
                              unsigned int n_ = n - 1;
                              if (n_ <= 0) {
                                _result = s;
                              } else {
                                unsigned int _x = n_ - 1;
                                _stack.push_back(_Call1{s, sep});
                                _stack.push_back(_Enter{n_});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            _result = append(_f._s0, append(_f._s1, _result));
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyStrings::string_chain_fuel(
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
    const std::shared_ptr<List<unsigned int>> _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
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
                              unsigned int fuel_ = fuel - 1;
                              if (n <= 0u) {
                                _result = List<unsigned int>::nil();
                              } else {
                                _stack.push_back(_Call1{s, sep, end_marker});
                                _stack.push_back(_Enter{
                                    (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            _result =
                                append(_f._s0,
                                       append(_f._s1, append(_result, _f._s2)));
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyStrings::string_chain(
    const std::shared_ptr<List<unsigned int>> &s, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<unsigned int>> &end_marker) {
  return string_chain_fuel(n, s, n, sep, end_marker);
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::reverse(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::cons(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        List<unsigned int>::nil())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{List<unsigned int>::cons(
                            _args.d_a0, List<unsigned int>::nil())});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = append(_result, _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyStrings::list_eq(const std::shared_ptr<List<unsigned int>> &l1,
                        const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>().d_a0 ==
             std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void {
                        _result = std::visit(
                            Overloaded{
                                [](const typename List<unsigned int>::Nil
                                       _args0) -> bool { return true; },
                                [](const typename List<unsigned int>::Cons
                                       _args0) -> bool { return false; }},
                            l2->v());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void { _result = false; },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(
                                      _Call1{_args.d_a0 == _args0.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                }},
                            l2->v());
                      }},
                  l1->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 && _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyStrings::is_palindrome(const std::shared_ptr<List<unsigned int>> &l) {
  return list_eq(l, reverse(l));
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::intersperse(const unsigned int sep,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        } else {
                          _head = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args.d_a0, nullptr);
                        auto _cell1 = List<unsigned int>::cons(sep, nullptr);
                        std::get<typename List<unsigned int>::Cons>(
                            _cell->v_mut())
                            .d_a1 = _cell1;
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell1;
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyStrings::intercalate(
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  ll = _f.ll;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil _args)
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Nil
                                        _args0) -> void {
                                  _result = _args.d_a0;
                                },
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = append(_f._s0, append(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyStrings::replicate(const unsigned int n, const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
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
      unsigned int n_ = _loop_n - 1;
      {
        auto _cell = List<unsigned int>::cons(x, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = std::move(n_);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyStrings::run_length_aux(const unsigned int current,
                               const unsigned int count,
                               const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_count = count;
  unsigned int _loop_current = current;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_loop_count == 0u) {
                if (_last) {
                  std::get<typename List<
                      std::pair<unsigned int, unsigned int>>::Cons>(
                      _last->v_mut())
                      .d_a1 =
                      List<std::pair<unsigned int, unsigned int>>::nil();
                } else {
                  _head = List<std::pair<unsigned int, unsigned int>>::nil();
                }
                _continue = false;
              } else {
                if (_last) {
                  std::get<typename List<
                      std::pair<unsigned int, unsigned int>>::Cons>(
                      _last->v_mut())
                      .d_a1 = List<std::pair<unsigned int, unsigned int>>::cons(
                      std::make_pair(std::move(_loop_current),
                                     std::move(_loop_count)),
                      List<std::pair<unsigned int, unsigned int>>::nil());
                } else {
                  _head = List<std::pair<unsigned int, unsigned int>>::cons(
                      std::make_pair(std::move(_loop_current),
                                     std::move(_loop_count)),
                      List<std::pair<unsigned int, unsigned int>>::nil());
                }
                _continue = false;
              }
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (_args.d_a0 == _loop_current) {
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_count = (std::move(_loop_count) + 1u);
                unsigned int _next_current = std::move(_loop_current);
                _loop_l = std::move(_next_l);
                _loop_count = std::move(_next_count);
                _loop_current = std::move(_next_current);
              } else {
                if (_loop_count == 0u) {
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_count = 1u;
                  unsigned int _next_current = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_count = std::move(_next_count);
                  _loop_current = std::move(_next_current);
                } else {
                  auto _cell =
                      List<std::pair<unsigned int, unsigned int>>::cons(
                          std::make_pair(std::move(_loop_current),
                                         std::move(_loop_count)),
                          nullptr);
                  if (_last) {
                    std::get<typename List<
                        std::pair<unsigned int, unsigned int>>::Cons>(
                        _last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_count = 1u;
                  unsigned int _next_current = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_count = std::move(_next_count);
                  _loop_current = std::move(_next_current);
                }
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyStrings::run_length_encode(
    const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> {
            return List<std::pair<unsigned int, unsigned int>>::nil();
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> {
            return run_length_aux(_args.d_a0, 1u, _args.d_a1);
          }},
      l->v());
}
