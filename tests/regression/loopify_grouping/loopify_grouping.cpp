#include <loopify_grouping.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::prepend_to_groups(
    const unsigned int x, const bool same,
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> groups) {
  if (same) {
    if (groups.use_count() == 1 && groups->v().index() == 1) {
      auto &_rf = std::get<1>(groups->v_mut());
      std::shared_ptr<List<unsigned int>> g = std::move(_rf.d_a0);
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> gs =
          std::move(_rf.d_a1);
      _rf.d_a0 = List<unsigned int>::cons(x, g);
      _rf.d_a1 = std::move(gs);
      return groups;
    } else {
      return std::visit(
          Overloaded{
              [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                      &)
                  -> std::shared_ptr<
                      List<std::shared_ptr<List<unsigned int>>>> {
                return List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::cons(x, List<unsigned int>::nil()),
                    List<std::shared_ptr<List<unsigned int>>>::nil());
              },
              [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                      &_args)
                  -> std::shared_ptr<
                      List<std::shared_ptr<List<unsigned int>>>> {
                return List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::cons(x, _args.d_a0), _args.d_a1);
              }},
          groups->v());
    }
  } else {
    return List<std::shared_ptr<List<unsigned int>>>::cons(
        List<unsigned int>::cons(x, List<unsigned int>::nil()), groups);
  }
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::group_fuel(const unsigned int fuel,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
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
                unsigned int fuel_ = fuel - 1;
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
                                    _stack.emplace_back(_Call1{_args, _args0});
                                    _stack.emplace_back(
                                        _Enter{List<unsigned int>::cons(
                                                   _args0.d_a0, _args0.d_a1),
                                               fuel_});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              const typename List<unsigned int>::Cons _args0 = _f._s1;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  rec_result = _result;
              _result = prepend_to_groups(_args.d_a0, _args.d_a0 == _args0.d_a0,
                                          std::move(rec_result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::group(const std::shared_ptr<List<unsigned int>> &l) {
  return group_fuel(l->length(), l);
}

__attribute__((pure)) bool
LoopifyGrouping::elem(const unsigned int x,
                      const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil &) {
                            _result = false;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons &_args) {
                            if (x == _args.d_a0) {
                              _result = true;
                              _continue = false;
                            } else {
                              _loop_l = _args.d_a1;
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGrouping::nub(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                        _result = List<unsigned int>::nil();
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{_args});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
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
LoopifyGrouping::remove_elem(const unsigned int x,
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

__attribute__((pure)) std::pair<std::pair<std::shared_ptr<List<unsigned int>>,
                                          std::shared_ptr<List<unsigned int>>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyGrouping::partition3(const unsigned int pivot,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<std::shared_ptr<List<unsigned int>>,
                      std::shared_ptr<List<unsigned int>>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
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
                        _result = std::make_pair(
                            std::make_pair(List<unsigned int>::nil(),
                                           List<unsigned int>::nil()),
                            List<unsigned int>::nil());
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{pivot, _args});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const unsigned int pivot = _f._s0;
              const typename List<unsigned int>::Cons _args = _f._s1;
              const std::pair<std::shared_ptr<List<unsigned int>>,
                              std::shared_ptr<List<unsigned int>>> &p =
                  _result.first;
              const std::shared_ptr<List<unsigned int>> &greater =
                  _result.second;
              const std::shared_ptr<List<unsigned int>> &less = p.first;
              const std::shared_ptr<List<unsigned int>> &equal = p.second;
              if (_args.d_a0 < pivot) {
                _result = std::make_pair(
                    std::make_pair(List<unsigned int>::cons(_args.d_a0, less),
                                   equal),
                    greater);
              } else {
                if (pivot < _args.d_a0) {
                  _result = std::make_pair(
                      std::make_pair(less, equal),
                      List<unsigned int>::cons(_args.d_a0, greater));
                } else {
                  _result = std::make_pair(
                      std::make_pair(
                          less, List<unsigned int>::cons(_args.d_a0, equal)),
                      greater);
                }
              }
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyGrouping::count_elem(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
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
                               if (x == _args.d_a0) {
                                 _stack.emplace_back(_Call1{1u});
                                 _stack.emplace_back(_Enter{_args.d_a1});
                               } else {
                                 _stack.emplace_back(_Enter{_args.d_a1});
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGrouping::group_pairs(const std::shared_ptr<List<unsigned int>> &l) {
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
                                  _loop_l = _args1.d_a1;
                                }},
                            _args.d_a1->v());
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}
