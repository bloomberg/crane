#include <loopify_list_windows.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int
LoopifyListWindows::len(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil &)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
                               _stack.emplace_back(_Call1{1u});
                               _stack.emplace_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::map_cons_helper(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    &) {
              if (_last) {
                std::get<
                    typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
              } else {
                _head = List<std::shared_ptr<List<unsigned int>>>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    &_args) {
              auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                  List<unsigned int>::cons(x, _args.d_a0), nullptr);
              if (_last) {
                std::get<
                    typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              _loop_ll = _args.d_a1;
            }},
        _loop_ll->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListWindows::drop(const unsigned int m,
                         std::shared_ptr<List<unsigned int>> xs) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_xs = xs;
  unsigned int _loop_m = m;
  bool _continue = true;
  while (_continue) {
    if (_loop_m <= 0) {
      _result = std::move(_loop_xs);
      _continue = false;
    } else {
      unsigned int m_ = _loop_m - 1;
      if (_loop_xs.use_count() == 1 && _loop_xs->v().index() == 0) {
        _result = _loop_xs;
        _continue = false;
      } else {
        std::visit(
            Overloaded{[&](const typename List<unsigned int>::Nil &) {
                         _result = List<unsigned int>::nil();
                         _continue = false;
                       },
                       [&](const typename List<unsigned int>::Cons &_args) {
                         std::shared_ptr<List<unsigned int>> _next_xs =
                             _args.d_a1;
                         unsigned int _next_m = m_;
                         _loop_xs = std::move(_next_xs);
                         _loop_m = std::move(_next_m);
                       }},
            _loop_xs->v());
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListWindows::span_eq(const unsigned int first,
                            std::shared_ptr<List<unsigned int>> lst) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> lst;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{lst});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> lst = _f.lst;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) -> void {
                        _result = std::make_pair(List<unsigned int>::nil(),
                                                 List<unsigned int>::nil());
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        if (first == _args.d_a0) {
                          _stack.emplace_back(_Call1{_args});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        } else {
                          _result = std::make_pair(List<unsigned int>::nil(),
                                                   std::move(lst));
                        }
                      }},
                  lst->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              const std::shared_ptr<List<unsigned int>> &s = _result.first;
              const std::shared_ptr<List<unsigned int>> &r = _result.second;
              _result =
                  std::make_pair(List<unsigned int>::cons(_args.d_a0, s), r);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListWindows::differences(const std::shared_ptr<List<unsigned int>> &l) {
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
                      [&](const typename List<unsigned int>::Cons &) {
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
                                [&](const typename List<unsigned int>::Cons
                                        &_args1) {
                                  auto _cell = List<unsigned int>::cons(
                                      (((_args1.d_a0 - _args.d_a0) > _args1.d_a0
                                            ? 0
                                            : (_args1.d_a0 - _args.d_a0))),
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
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListWindows::sliding_pairs(
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<
                    typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                    _last->v_mut())
                    .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
              } else {
                _head = List<std::pair<unsigned int, unsigned int>>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        if (_last) {
                          std::get<typename List<
                              std::pair<unsigned int, unsigned int>>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<
                              std::pair<unsigned int, unsigned int>>::nil();
                        } else {
                          _head = List<
                              std::pair<unsigned int, unsigned int>>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons &) {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &) {
                                  if (_last) {
                                    std::get<typename List<std::pair<
                                        unsigned int, unsigned int>>::Cons>(
                                        _last->v_mut())
                                        .d_a1 =
                                        List<std::pair<unsigned int,
                                                       unsigned int>>::nil();
                                  } else {
                                    _head =
                                        List<std::pair<unsigned int,
                                                       unsigned int>>::nil();
                                  }
                                  _continue = false;
                                },
                                [&](const typename List<unsigned int>::Cons
                                        &_args1) {
                                  auto _cell = List<
                                      std::pair<unsigned int, unsigned int>>::
                                      cons(std::make_pair(_args.d_a0,
                                                          _args1.d_a0),
                                           nullptr);
                                  if (_last) {
                                    std::get<typename List<std::pair<
                                        unsigned int, unsigned int>>::Cons>(
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
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::inits(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::nil()) _s0;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
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
                        _stack.emplace_back(
                            _Call1{List<unsigned int>::nil(), _args.d_a0});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::cons(
                  _f._s0, map_cons_helper(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::tails(std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<
                    typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::nil(),
                    List<std::shared_ptr<List<unsigned int>>>::nil());
              } else {
                _head = List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::nil(),
                    List<std::shared_ptr<List<unsigned int>>>::nil());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                  _loop_l, nullptr);
              if (_last) {
                std::get<
                    typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              _loop_l = _args.d_a1;
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListWindows::take(const unsigned int n,
                         const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
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
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_n = n_;
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::windows_fuel(const unsigned int fuel, const unsigned int n,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          _head = List<std::shared_ptr<List<unsigned int>>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
                } else {
                  _head = List<std::shared_ptr<List<unsigned int>>>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &_args) {
                if (len(_loop_l) < n) {
                  if (_last) {
                    std::get<typename List<
                        std::shared_ptr<List<unsigned int>>>::Cons>(
                        _last->v_mut())
                        .d_a1 =
                        List<std::shared_ptr<List<unsigned int>>>::nil();
                  } else {
                    _head = List<std::shared_ptr<List<unsigned int>>>::nil();
                  }
                  _continue = false;
                } else {
                  auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                      take(n, _loop_l), nullptr);
                  if (_last) {
                    std::get<typename List<
                        std::shared_ptr<List<unsigned int>>>::Cons>(
                        _last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_fuel = fuel_;
                  _loop_l = std::move(_next_l);
                  _loop_fuel = std::move(_next_fuel);
                }
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::windows(const unsigned int n,
                            const std::shared_ptr<List<unsigned int>> &l) {
  return windows_fuel(len(l), n, l);
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::chunks_fuel(const unsigned int fuel, const unsigned int n,
                                const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          _head = List<std::shared_ptr<List<unsigned int>>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
                } else {
                  _head = List<std::shared_ptr<List<unsigned int>>>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &) {
                std::shared_ptr<List<unsigned int>> chunk = take(n, _loop_l);
                std::shared_ptr<List<unsigned int>> rest = drop(n, _loop_l);
                auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                    chunk, nullptr);
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = rest;
                unsigned int _next_fuel = fuel_;
                _loop_l = std::move(_next_l);
                _loop_fuel = std::move(_next_fuel);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::chunks(const unsigned int n,
                           const std::shared_ptr<List<unsigned int>> &l) {
  return chunks_fuel(len(l), n, l);
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::group_fuel(const unsigned int fuel,
                               const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          _head = List<std::shared_ptr<List<unsigned int>>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
                } else {
                  _head = List<std::shared_ptr<List<unsigned int>>>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &_args) {
                auto _cs = span_eq(_args.d_a0, _args.d_a1);
                const std::shared_ptr<List<unsigned int>> &same = _cs.first;
                const std::shared_ptr<List<unsigned int>> &rest = _cs.second;
                auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::cons(_args.d_a0, same), nullptr);
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = rest;
                unsigned int _next_fuel = fuel_;
                _loop_l = std::move(_next_l);
                _loop_fuel = std::move(_next_fuel);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::group(const std::shared_ptr<List<unsigned int>> &l) {
  return group_fuel(len(l), l);
}
