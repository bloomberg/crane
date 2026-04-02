#include <loopify_combinatorics.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Consolidated combinatorial algorithms.
/// remove x l removes first occurrence of x from list.
std::shared_ptr<List<unsigned int>>
LoopifyCombinatorics::remove(const unsigned int x,
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
              if (x == _args.d_a0) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _args.d_a1;
                } else {
                  _head = _args.d_a1;
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
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// Helper: prepend x to each list in lsts.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::map_cons(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_lsts = lsts;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    _args) {
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
                    _args) {
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
              _loop_lsts = _args.d_a1;
            }},
        _loop_lsts->v());
  }
  return _head;
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function that handles both the choice
/// iteration and the recursive subproblem, enabling full loopification.
/// The match on remaining is hoisted out of the let-binding so that all
/// recursive calls appear at the top level of each branch.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::perms_choices_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &choices,
    const std::shared_ptr<List<unsigned int>> &orig) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> orig;
    const std::shared_ptr<List<unsigned int>> choices;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(map_cons(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil()))) _s0;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    std::shared_ptr<List<unsigned int>> _s1;
    unsigned int _s2;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s3;
  };

  struct _Call3 {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{orig, choices, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> orig = _f.orig;
              const std::shared_ptr<List<unsigned int>> choices = _f.choices;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<std::shared_ptr<List<unsigned int>>>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result =
                              List<std::shared_ptr<List<unsigned int>>>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::shared_ptr<List<unsigned int>> remaining =
                              remove(_args.d_a0, orig);
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _stack.push_back(_Call1{map_cons(
                                        _args.d_a0,
                                        List<std::shared_ptr<
                                            List<unsigned int>>>::
                                            cons(List<unsigned int>::nil(),
                                                 List<std::shared_ptr<List<
                                                     unsigned int>>>::nil()))});
                                    _stack.push_back(
                                        _Enter{orig, _args.d_a1, f});
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    _stack.push_back(_Call2{
                                        remaining, remaining, f, _args.d_a0});
                                    _stack.push_back(
                                        _Enter{orig, _args.d_a1, f});
                                  }},
                              remaining->v());
                        }},
                    choices->v());
              }
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result, _f._s3});
              _stack.push_back(_Enter{_f._s0, _f._s1, _f._s2});
            },
            [&](_Call3 _f) {
              _result = map_cons(_f._s1, _result)->app(_f._s0);
            }},
        _frame);
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of a list.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::permutations_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
            return List<std::shared_ptr<List<unsigned int>>>::cons(
                List<unsigned int>::nil(),
                List<std::shared_ptr<List<unsigned int>>>::nil());
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
            return perms_choices_fuel(fuel, l, l);
          }},
      l->v());
}

__attribute__((pure)) unsigned int
LoopifyCombinatorics::len_list(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyCombinatorics::factorial_impl(const unsigned int n) {
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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::permutations(
    const std::shared_ptr<List<unsigned int>> &l) {
  return permutations_fuel(factorial_impl(len_list(l)), l);
}

/// subsequences l generates all subsequences (subsets preserving order).
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::subsequences(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
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
                          -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::nil(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    nil());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest =
                  _result;
              std::function<std::shared_ptr<
                  List<std::shared_ptr<List<unsigned int>>>>(
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
                  map_prepend;
              map_prepend =
                  [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                          lst)
                  -> std::shared_ptr<
                      List<std::shared_ptr<List<unsigned int>>>> {
                struct _Enter {
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                      lst;
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
                _stack.push_back(_Enter{lst});
                while (!_stack.empty()) {
                  _Frame _frame = std::move(_stack.back());
                  _stack.pop_back();
                  std::visit(
                      Overloaded{
                          [&](_Enter _f) {
                            std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>>
                                lst = _f.lst;
                            std::visit(
                                Overloaded{
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Nil _args0)
                                        -> void {
                                      _result = List<std::shared_ptr<
                                          List<unsigned int>>>::nil();
                                    },
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Cons _args0)
                                        -> void {
                                      _stack.push_back(
                                          _Call1{List<unsigned int>::cons(
                                              _args.d_a0, _args0.d_a0)});
                                      _stack.push_back(_Enter{_args0.d_a1});
                                    }},
                                lst->v());
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
              _result = rest->app(map_prepend(rest));
            }},
        _frame);
  }
  return _result;
}

/// Helper for cartesian product.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyCombinatorics::map_pairs(const unsigned int y,
                                const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
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
            [&](const typename List<unsigned int>::Cons _args) {
              auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
                  std::make_pair(_args.d_a0, y), nullptr);
              if (_last) {
                std::get<
                    typename List<std::pair<unsigned int, unsigned int>>::Cons>(
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

/// cartesian l1 l2 Cartesian product of two lists.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyCombinatorics::cartesian(const std::shared_ptr<List<unsigned int>> &l1,
                                const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
  };

  struct _Call1 {
    decltype(map_pairs(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const std::shared_ptr<List<unsigned int>> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::nil();
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{map_pairs(_args.d_a0, l1)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l2->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

/// power_set l generates the power set (all subsets).
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::power_set(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
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
                          -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::nil(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    nil());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest =
                  _result;
              std::function<std::shared_ptr<
                  List<std::shared_ptr<List<unsigned int>>>>(
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
                  map_add_x;
              map_add_x =
                  [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                          lst)
                  -> std::shared_ptr<
                      List<std::shared_ptr<List<unsigned int>>>> {
                struct _Enter {
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                      lst;
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
                _stack.push_back(_Enter{lst});
                while (!_stack.empty()) {
                  _Frame _frame = std::move(_stack.back());
                  _stack.pop_back();
                  std::visit(
                      Overloaded{
                          [&](_Enter _f) {
                            std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>>
                                lst = _f.lst;
                            std::visit(
                                Overloaded{
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Nil _args0)
                                        -> void {
                                      _result = List<std::shared_ptr<
                                          List<unsigned int>>>::nil();
                                    },
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Cons _args0)
                                        -> void {
                                      _stack.push_back(
                                          _Call1{List<unsigned int>::cons(
                                              _args.d_a0, _args0.d_a0)});
                                      _stack.push_back(_Enter{_args0.d_a1});
                                    }},
                                lst->v());
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
              _result = rest->app(map_add_x(rest));
            }},
        _frame);
  }
  return _result;
}

/// insert_everywhere x l inserts x at every position in l.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::insert_everywhere(const unsigned int x,
                                        std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    std::shared_ptr<List<unsigned int>> _s1;
    const unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::cons(
                                    x, List<unsigned int>::nil()),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    nil());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args, l, x});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> l = _f._s1;
              const unsigned int x = _f._s2;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest =
                  _result;
              std::function<std::shared_ptr<
                  List<std::shared_ptr<List<unsigned int>>>>(
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
                  prepend_y;
              prepend_y =
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
                                            List<unsigned int>>>::Nil _args0)
                                        -> void {
                                      _result = List<std::shared_ptr<
                                          List<unsigned int>>>::nil();
                                    },
                                    [&](const typename List<std::shared_ptr<
                                            List<unsigned int>>>::Cons _args0)
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
              _result = List<std::shared_ptr<List<unsigned int>>>::cons(
                  List<unsigned int>::cons(x, l), prepend_y(rest));
            }},
        _frame);
  }
  return _result;
}

/// Helper: check if element is in list.
__attribute__((pure)) bool
LoopifyCombinatorics::elem(const unsigned int x,
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
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = false; },
                             [&](const typename List<unsigned int>::Cons _args)
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

/// Helper: list length.
__attribute__((pure)) unsigned int
LoopifyCombinatorics::len_impl(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

/// dedup l removes all duplicates (keeps first occurrence).
std::shared_ptr<List<unsigned int>>
LoopifyCombinatorics::dedup_fuel(const unsigned int fuel,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                _result = List<unsigned int>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void { _result = List<unsigned int>::nil(); },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args});
                          _stack.push_back(_Enter{_args.d_a1, f});
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> rest = _result;
              if (elem(_args.d_a0, rest)) {
                _result = std::move(rest);
              } else {
                _result = List<unsigned int>::cons(_args.d_a0, rest);
              }
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyCombinatorics::dedup(const std::shared_ptr<List<unsigned int>> &l) {
  return dedup_fuel(len_impl(l), l);
}
