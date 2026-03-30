#include <loopify_pairs.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Consolidated UNIQUE pair/tuple operations.
/// unzip l splits list of nat pairs into pair of lists.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
          std::shared_ptr<LoopifyPairs::list<unsigned int>>>
LoopifyPairs::unzip(
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
        l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
            std::shared_ptr<LoopifyPairs::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyPairs::list<
                          std::pair<unsigned int, unsigned int>>::Nil _args)
                          -> void {
                        _result = std::make_pair(list<unsigned int>::nil(),
                                                 list<unsigned int>::nil());
                      },
                      [&](const typename LoopifyPairs::list<
                          std::pair<unsigned int, unsigned int>>::Cons _args)
                          -> void {
                        unsigned int x = _args.d_a0.first;
                        unsigned int y = _args.d_a0.second;
                        _stack.push_back(_Call1{y, x});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              unsigned int y = _f._s0;
              unsigned int x = _f._s1;
              std::shared_ptr<LoopifyPairs::list<unsigned int>> xs =
                  _result.first;
              std::shared_ptr<LoopifyPairs::list<unsigned int>> ys =
                  _result.second;
              _result = std::make_pair(list<unsigned int>::cons(x, xs),
                                       list<unsigned int>::cons(y, ys));
            }},
        _frame);
  }
  return _result;
}

/// partition3 pivot l three-way partition around pivot.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
          std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
                    std::shared_ptr<LoopifyPairs::list<unsigned int>>>>
LoopifyPairs::partition3(
    const unsigned int pivot,
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    const typename LoopifyPairs::list<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
            std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
                      std::shared_ptr<LoopifyPairs::list<unsigned int>>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyPairs::list<unsigned int>::Nil
                              _args) -> void {
                        _result = std::make_pair(
                            list<unsigned int>::nil(),
                            std::make_pair(list<unsigned int>::nil(),
                                           list<unsigned int>::nil()));
                      },
                      [&](const typename LoopifyPairs::list<unsigned int>::Cons
                              _args) -> void {
                        _stack.push_back(_Call1{pivot, _args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const unsigned int pivot = _f._s0;
              const typename LoopifyPairs::list<unsigned int>::Cons _args =
                  _f._s1;
              std::shared_ptr<LoopifyPairs::list<unsigned int>> lt =
                  _result.first;
              std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
                        std::shared_ptr<LoopifyPairs::list<unsigned int>>>
                  p = _result.second;
              std::shared_ptr<LoopifyPairs::list<unsigned int>> eq = p.first;
              std::shared_ptr<LoopifyPairs::list<unsigned int>> gt = p.second;
              if (_args.d_a0 < pivot) {
                _result =
                    std::make_pair(list<unsigned int>::cons(_args.d_a0, lt),
                                   std::make_pair(eq, gt));
              } else {
                if (_args.d_a0 == pivot) {
                  _result = std::make_pair(
                      lt, std::make_pair(
                              list<unsigned int>::cons(_args.d_a0, eq), gt));
                } else {
                  _result = std::make_pair(
                      lt, std::make_pair(
                              eq, list<unsigned int>::cons(_args.d_a0, gt)));
                }
              }
            }},
        _frame);
  }
  return _result;
}

/// min_max l finds both min and max in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyPairs::min_max(
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPairs::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyPairs::list<unsigned int>::Nil
                              _args) -> void {
                        _result = std::make_pair(0u, 0u);
                      },
                      [&](const typename LoopifyPairs::list<unsigned int>::Cons
                              _args) -> void {
                        std::visit(
                            Overloaded{[&](const typename LoopifyPairs::list<
                                           unsigned int>::Nil _args0) -> void {
                                         _result = std::make_pair(_args.d_a0,
                                                                  _args.d_a0);
                                       },
                                       [&](const typename LoopifyPairs::list<
                                           unsigned int>::Cons _args0) -> void {
                                         _stack.push_back(_Call1{_args});
                                         _stack.push_back(_Enter{_args.d_a1});
                                       }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyPairs::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int mn = _result.first;
              unsigned int mx = _result.second;
              _result = std::make_pair(
                  [&]() {
                    if (_args.d_a0 <= mn) {
                      return _args.d_a0;
                    } else {
                      return mn;
                    }
                  }(),
                  [&]() {
                    if (mx <= _args.d_a0) {
                      return _args.d_a0;
                    } else {
                      return mx;
                    }
                  }());
            }},
        _frame);
  }
  return _result;
}

/// sum_and_count computes both in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyPairs::sum_and_count(
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPairs::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyPairs::list<unsigned int>::Nil
                              _args) -> void {
                        _result = std::make_pair(0u, 0u);
                      },
                      [&](const typename LoopifyPairs::list<unsigned int>::Cons
                              _args) -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyPairs::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int s = _result.first;
              unsigned int c = _result.second;
              _result = std::make_pair((_args.d_a0 + s), (c + 1));
            }},
        _frame);
  }
  return _result;
}

/// sum_prod_count triple accumulator.
__attribute__((pure))
std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
LoopifyPairs::sum_prod_count(
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPairs::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, std::pair<unsigned int, unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyPairs::list<unsigned int>::Nil
                              _args) -> void {
                        _result = std::make_pair(0u, std::make_pair(1u, 0u));
                      },
                      [&](const typename LoopifyPairs::list<unsigned int>::Cons
                              _args) -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyPairs::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int s = _result.first;
              std::pair<unsigned int, unsigned int> p0 = _result.second;
              unsigned int p = p0.first;
              unsigned int c = p0.second;
              _result = std::make_pair(
                  (_args.d_a0 + s), std::make_pair((_args.d_a0 * p), (c + 1)));
            }},
        _frame);
  }
  return _result;
}

/// lookup_all key l finds all values associated with key.
std::shared_ptr<LoopifyPairs::list<unsigned int>> LoopifyPairs::lookup_all(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<LoopifyPairs::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPairs::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyPairs::list<
                std::pair<unsigned int, unsigned int>>::Nil _args) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyPairs::list<
                std::pair<unsigned int, unsigned int>>::Cons _args) {
              unsigned int k = _args.d_a0.first;
              unsigned int v = _args.d_a0.second;
              if (k == key) {
                auto _cell = list<unsigned int>::cons(v, nullptr);
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
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

/// swap_pairs l swaps elements in each pair.
std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
LoopifyPairs::swap_pairs(
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _head{};
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _last{};
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyPairs::list<
                std::pair<unsigned int, unsigned int>>::Nil _args) {
              if (_last) {
                std::get<
                    typename list<std::pair<unsigned int, unsigned int>>::Cons>(
                    _last->v_mut())
                    .d_a1 = list<std::pair<unsigned int, unsigned int>>::nil();
              } else {
                _head = list<std::pair<unsigned int, unsigned int>>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyPairs::list<
                std::pair<unsigned int, unsigned int>>::Cons _args) {
              unsigned int a = _args.d_a0.first;
              unsigned int b = _args.d_a0.second;
              auto _cell = list<std::pair<unsigned int, unsigned int>>::cons(
                  std::make_pair(b, a), nullptr);
              if (_last) {
                std::get<
                    typename list<std::pair<unsigned int, unsigned int>>::Cons>(
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
