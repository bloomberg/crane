#include <loopify_special_recursion.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> LoopifySpecialRecursion::process_twice_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
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
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void { _result = List<unsigned int>::nil(); },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args, fuel_});
                          _stack.push_back(_Enter{_args.d_a1, fuel_});
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              unsigned int fuel_ = _f._s1;
              std::shared_ptr<List<unsigned int>> first = _result;
              _stack.push_back(_Call2{_args});
              _stack.push_back(_Enter{std::move(first), fuel_});
            },
            [&](_Call2 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> second = _result;
              _result = List<unsigned int>::cons(_args.d_a0, second);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifySpecialRecursion::process_twice(
    const std::shared_ptr<List<unsigned int>> &l) {
  return process_twice_fuel((l->length() * l->length()), l);
}

std::shared_ptr<List<unsigned int>> LoopifySpecialRecursion::double_append(
    const std::shared_ptr<List<unsigned int>> &l1,
    std::shared_ptr<List<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = std::move(l2); },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{_args});
                               _stack.push_back(
                                   _Enter{std::move(l2), _args.d_a1});
                             }},
                  l1->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> rest = _result;
              _result = List<unsigned int>::cons(_args.d_a0, rest->app(rest));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifySpecialRecursion::remove_if_sum_even(
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
              unsigned int next_val = std::visit(
                  Overloaded{[](const typename List<unsigned int>::Nil _args0)
                                 -> unsigned int { return 0u; },
                             [](const typename List<unsigned int>::Cons _args0)
                                 -> unsigned int { return _args0.d_a0; }},
                  _args.d_a1->v());
              if ((2u ? (_args.d_a0 + std::move(next_val)) % 2u
                      : (_args.d_a0 + std::move(next_val))) == 0u) {
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

std::shared_ptr<List<unsigned int>>
LoopifySpecialRecursion::reverse_insert(const unsigned int x,
                                        std::shared_ptr<List<unsigned int>> l) {
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
                    .d_a1 =
                    List<unsigned int>::cons(x, List<unsigned int>::nil());
              } else {
                _head = List<unsigned int>::cons(x, List<unsigned int>::nil());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (_args.d_a0 < x) {
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
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(x, _loop_l);
                } else {
                  _head = List<unsigned int>::cons(x, _loop_l);
                }
                _continue = false;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifySpecialRecursion::collect_sorted(
    const std::shared_ptr<LoopifySpecialRecursion::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifySpecialRecursion::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifySpecialRecursion::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 const typename LoopifySpecialRecursion::tree::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(std::declval<
                 const typename LoopifySpecialRecursion::tree::Node &>()
                 .d_a1) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifySpecialRecursion::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifySpecialRecursion::tree::Leaf
                              _args) -> void {
                        _result = List<unsigned int>::nil();
                      },
                      [&](const typename LoopifySpecialRecursion::tree::Node
                              _args) -> void {
                        _stack.push_back(_Call1{_args.d_a0, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _result = _result->app(List<unsigned int>::cons(_f._s1, _f._s0));
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifySpecialRecursion::sum_odd_indices_aux(
    const std::shared_ptr<List<unsigned int>> &l, const unsigned int idx) {
  struct _Enter {
    const unsigned int idx;
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{idx, l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int idx = _f.idx;
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        if ((2u ? idx % 2u : idx) == 1u) {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{(idx + 1u), _args.d_a1});
                        } else {
                          _stack.push_back(_Enter{(idx + 1u), _args.d_a1});
                        }
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifySpecialRecursion::sum_odd_indices(
    const std::shared_ptr<List<unsigned int>> &l) {
  return sum_odd_indices_aux(l, 0u);
}

__attribute__((pure)) unsigned int LoopifySpecialRecursion::categorize_by(
    const unsigned int k, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(3u) _s0;
  };

  struct _Call2 {
    decltype(2u) _s0;
  };

  struct _Call3 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
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
                               if (k < _args.d_a0) {
                                 _stack.push_back(_Call1{3u});
                                 _stack.push_back(_Enter{_args.d_a1});
                               } else {
                                 if (_args.d_a0 == k) {
                                   _stack.push_back(_Call2{2u});
                                   _stack.push_back(_Enter{_args.d_a1});
                                 } else {
                                   _stack.push_back(_Call3{1u});
                                   _stack.push_back(_Enter{_args.d_a1});
                                 }
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); },
                   [&](_Call2 _f) { _result = (_f._s0 + _result); },
                   [&](_Call3 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySpecialRecursion::between(const unsigned int lo, const unsigned int hi,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_hi = hi;
  unsigned int _loop_lo = lo;
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
              if (_loop_lo <= _args.d_a0) {
                if (_args.d_a0 <= _loop_hi) {
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
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_hi = std::move(_loop_hi);
                  unsigned int _next_lo = std::move(_loop_lo);
                  _loop_l = std::move(_next_l);
                  _loop_hi = std::move(_next_hi);
                  _loop_lo = std::move(_next_lo);
                }
              } else {
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_hi = std::move(_loop_hi);
                unsigned int _next_lo = std::move(_loop_lo);
                _loop_l = std::move(_next_l);
                _loop_hi = std::move(_next_hi);
                _loop_lo = std::move(_next_lo);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifySpecialRecursion::merge_levels(
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
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}
