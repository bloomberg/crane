#include <loopify_hofs.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool
LoopifyHofs::is_prefix_of(const std::shared_ptr<List<unsigned int>> &l1,
                          const std::shared_ptr<List<unsigned int>> &l2) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = false;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
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

/// lookup_all key l finds all values associated with key in association list.
std::shared_ptr<List<unsigned int>> LoopifyHofs::lookup_all(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Nil
                    _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Cons
                    _args) {
              unsigned int k = _args.d_a0.first;
              unsigned int v = _args.d_a0.second;
              if (k == key) {
                auto _cell = List<unsigned int>::cons(v, nullptr);
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

/// Helper: get head of list with default.
__attribute__((pure)) unsigned int
LoopifyHofs::head_default(const unsigned int default0,
                          const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return std::move(default0);
          },
          [](const typename List<unsigned int>::Cons _args) -> unsigned int {
            return _args.d_a0;
          }},
      l->v());
}

/// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyHofs::subsequences(const std::shared_ptr<List<unsigned int>> &l) {
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
                  map_cons_x;
              map_cons_x =
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
              _result = rest->app(map_cons_x(rest));
            }},
        _frame);
  }
  return _result;
}

/// Helper: pair element with all elements in list.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyHofs::pair_with_all(const unsigned int x,
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
                  std::make_pair(x, _args.d_a0), nullptr);
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

/// cartesian l1 l2 computes cartesian product of two lists.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyHofs::cartesian(const std::shared_ptr<List<unsigned int>> &l1,
                       const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(pair_with_all(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const std::shared_ptr<List<unsigned int>> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::nil();
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{pair_with_all(_args.d_a0, l2)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l1->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

/// longest_run l finds the longest consecutive run of equal elements.
/// Matches on recursive result to decide behavior.
std::shared_ptr<List<unsigned int>>
LoopifyHofs::longest_run_fuel(const unsigned int fuel,
                              std::shared_ptr<List<unsigned int>> l) {
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
              std::move(_loop_l);
        } else {
          _head = std::move(_loop_l);
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
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
                          if (_args.d_a0 == _args0.d_a0) {
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
                            std::shared_ptr<List<unsigned int>> _next_l =
                                List<unsigned int>::cons(_args0.d_a0,
                                                         _args0.d_a1);
                            unsigned int _next_fuel = std::move(f);
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
                          } else {
                            std::shared_ptr<List<unsigned int>> rec_result =
                                longest_run_fuel(std::move(f),
                                                 List<unsigned int>::cons(
                                                     _args0.d_a0, _args0.d_a1));
                            if (_last) {
                              std::get<typename List<unsigned int>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = std::visit(
                                  Overloaded{
                                      [&](const typename List<unsigned int>::Nil
                                              _args1)
                                          -> std::shared_ptr<
                                              List<unsigned int>> {
                                        return List<unsigned int>::cons(
                                            _args.d_a0,
                                            List<unsigned int>::nil());
                                      },
                                      [&](const typename List<
                                          unsigned int>::Cons _args1)
                                          -> std::shared_ptr<
                                              List<unsigned int>> {
                                        if (_args.d_a0 == _args1.d_a0) {
                                          return std::move(rec_result);
                                        } else {
                                          return std::move(rec_result);
                                        }
                                      }},
                                  rec_result->v());
                            } else {
                              _head = std::visit(
                                  Overloaded{
                                      [&](const typename List<unsigned int>::Nil
                                              _args1)
                                          -> std::shared_ptr<
                                              List<unsigned int>> {
                                        return List<unsigned int>::cons(
                                            _args.d_a0,
                                            List<unsigned int>::nil());
                                      },
                                      [&](const typename List<
                                          unsigned int>::Cons _args1)
                                          -> std::shared_ptr<
                                              List<unsigned int>> {
                                        if (_args.d_a0 == _args1.d_a0) {
                                          return std::move(rec_result);
                                        } else {
                                          return std::move(rec_result);
                                        }
                                      }},
                                  rec_result->v());
                            }
                            _continue = false;
                          }
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyHofs::longest_run(const std::shared_ptr<List<unsigned int>> &l) {
  return longest_run_fuel(l->length(), l);
}

/// power_set l generates all subsets.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyHofs::power_set(const std::shared_ptr<List<unsigned int>> &l) {
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
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> sub =
                  _result;
              std::function<std::shared_ptr<
                  List<std::shared_ptr<List<unsigned int>>>>(
                  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
                  map_cons_x;
              map_cons_x =
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
              _result = sub->app(map_cons_x(sub));
            }},
        _frame);
  }
  return _result;
}
