#include <loopify_list_of_lists.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::intercalate(
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
  _stack.emplace_back(_Enter{ll});
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
                          std::shared_ptr<List<unsigned int>>>::Nil &) -> void {
                        _result = List<unsigned int>::nil();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Nil &)
                                    -> void { _result = _args.d_a0; },
                                [&](const typename List<std::shared_ptr<
                                        List<unsigned int>>>::Cons &) -> void {
                                  _stack.emplace_back(_Call1{_args.d_a0, sep});
                                  _stack.emplace_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_f._s1->app(_result)); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::map_hd(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        _loop_ll = _args.d_a1;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args0.d_a0, nullptr);
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_ll = _args.d_a1;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListOfLists::map_tl(
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
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        _loop_ll = _args.d_a1;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        auto _cell =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                _args0.d_a1, nullptr);
                        if (_last) {
                          std::get<typename List<
                              std::shared_ptr<List<unsigned int>>>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_ll = _args.d_a1;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _head;
}

__attribute__((pure)) bool LoopifyListOfLists::all_empty(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  bool _result;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    &) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    &_args) {
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil &) {
                               _loop_ll = _args.d_a1;
                             },
                             [&](const typename List<unsigned int>::Cons &) {
                               _result = false;
                               _continue = false;
                             }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListOfLists::transpose_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
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
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) {
                          if (_last) {
                            std::get<typename List<
                                std::shared_ptr<List<unsigned int>>>::Cons>(
                                _last->v_mut())
                                .d_a1 = List<
                                std::shared_ptr<List<unsigned int>>>::nil();
                          } else {
                            _head = List<
                                std::shared_ptr<List<unsigned int>>>::nil();
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons &) {
                          if (all_empty(_loop_ll)) {
                            if (_last) {
                              std::get<typename List<
                                  std::shared_ptr<List<unsigned int>>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = List<
                                  std::shared_ptr<List<unsigned int>>>::nil();
                            } else {
                              _head = List<
                                  std::shared_ptr<List<unsigned int>>>::nil();
                            }
                            _continue = false;
                          } else {
                            std::shared_ptr<List<unsigned int>> heads =
                                map_hd(_loop_ll);
                            std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>>
                                tails = map_tl(_loop_ll);
                            auto _cell =
                                List<std::shared_ptr<List<unsigned int>>>::cons(
                                    heads, nullptr);
                            if (_last) {
                              std::get<typename List<
                                  std::shared_ptr<List<unsigned int>>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>>
                                _next_ll = tails;
                            unsigned int _next_fuel = fuel_;
                            _loop_ll = std::move(_next_ll);
                            _loop_fuel = std::move(_next_fuel);
                          }
                        }},
                    _args.d_a0->v());
              }},
          _loop_ll->v());
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int
LoopifyListOfLists::list_len(const std::shared_ptr<List<unsigned int>> &l) {
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

__attribute__((pure)) unsigned int LoopifyListOfLists::total_length(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(list_len(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
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
                          std::shared_ptr<List<unsigned int>>>::Nil &) -> void {
                        _result = 0u;
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{list_len(_args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListOfLists::transpose(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  return transpose_fuel(total_length(ll), ll);
}

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::flatten(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
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
                          std::shared_ptr<List<unsigned int>>>::Nil &) -> void {
                        _result = List<unsigned int>::nil();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{_args.d_a0});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListOfLists::count_total(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(list_len(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
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
                          std::shared_ptr<List<unsigned int>>>::Nil &) -> void {
                        _result = 0u;
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{list_len(_args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::firsts(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        _loop_ll = _args.d_a1;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args0.d_a0, nullptr);
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_ll = _args.d_a1;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _head;
}

__attribute__((pure)) bool LoopifyListOfLists::all_nil(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  bool _result;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    &) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    &_args) {
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil &) {
                               _loop_ll = _args.d_a1;
                             },
                             [&](const typename List<unsigned int>::Cons &) {
                               _result = false;
                               _continue = false;
                             }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _result;
}

std::shared_ptr<List<std::pair<std::shared_ptr<List<unsigned int>>,
                               std::shared_ptr<List<unsigned int>>>>>
LoopifyListOfLists::zip_lists(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll1,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll2) {
  std::shared_ptr<List<std::pair<std::shared_ptr<List<unsigned int>>,
                                 std::shared_ptr<List<unsigned int>>>>>
      _head{};
  std::shared_ptr<List<std::pair<std::shared_ptr<List<unsigned int>>,
                                 std::shared_ptr<List<unsigned int>>>>>
      _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll2 = ll2;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll1 = ll1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    &) {
              if (_last) {
                std::get<typename List<
                    std::pair<std::shared_ptr<List<unsigned int>>,
                              std::shared_ptr<List<unsigned int>>>>::Cons>(
                    _last->v_mut())
                    .d_a1 =
                    List<std::pair<std::shared_ptr<List<unsigned int>>,
                                   std::shared_ptr<List<unsigned int>>>>::nil();
              } else {
                _head =
                    List<std::pair<std::shared_ptr<List<unsigned int>>,
                                   std::shared_ptr<List<unsigned int>>>>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil &) {
                        if (_last) {
                          std::get<typename List<std::pair<
                              std::shared_ptr<List<unsigned int>>,
                              std::shared_ptr<List<unsigned int>>>>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<std::pair<
                              std::shared_ptr<List<unsigned int>>,
                              std::shared_ptr<List<unsigned int>>>>::nil();
                        } else {
                          _head = List<std::pair<
                              std::shared_ptr<List<unsigned int>>,
                              std::shared_ptr<List<unsigned int>>>>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args0) {
                        auto _cell = List<
                            std::pair<std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>::
                            cons(std::make_pair(_args.d_a0, _args0.d_a0),
                                 nullptr);
                        if (_last) {
                          std::get<typename List<std::pair<
                              std::shared_ptr<List<unsigned int>>,
                              std::shared_ptr<List<unsigned int>>>>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        std::shared_ptr<
                            List<std::shared_ptr<List<unsigned int>>>>
                            _next_ll2 = _args0.d_a1;
                        std::shared_ptr<
                            List<std::shared_ptr<List<unsigned int>>>>
                            _next_ll1 = _args.d_a1;
                        _loop_ll2 = std::move(_next_ll2);
                        _loop_ll1 = std::move(_next_ll1);
                      }},
                  _loop_ll2->v());
            }},
        _loop_ll1->v());
  }
  return _head;
}

__attribute__((pure)) unsigned int LoopifyListOfLists::max_length(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(list_len(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
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
                          std::shared_ptr<List<unsigned int>>>::Nil &) -> void {
                        _result = 0u;
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{list_len(_args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = std::max(_f._s0, _result); }},
        _frame);
  }
  return _result;
}
