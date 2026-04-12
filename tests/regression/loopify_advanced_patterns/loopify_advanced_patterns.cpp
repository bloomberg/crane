#include <loopify_advanced_patterns.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::len_impl(
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
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
                               _stack.push_back(_Call1{1u});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedPatterns::as_guard(
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
              if (3u < len_impl(_loop_l)) {
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

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::multi_guard(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
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
                             [&](const typename List<unsigned int>::Nil &)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
                               if (10u < _args.d_a0) {
                                 _stack.push_back(_Call1{_args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               } else {
                                 if (0u < _args.d_a0) {
                                   _stack.push_back(_Enter{_args.d_a1});
                                 } else {
                                   _stack.push_back(_Call2{1u});
                                   _stack.push_back(_Enter{_args.d_a1});
                                 }
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); },
                   [&](_Call2 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::four_elem(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        ((std::declval<const typename List<unsigned int>::Cons &>().d_a0 +
          std::declval<const typename List<unsigned int>::Cons &>().d_a0) +
         std::declval<const typename List<unsigned int>::Cons &>().d_a0) +
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                      [&](const typename List<unsigned int>::Nil &) -> void {
                        _result = 0u;
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &)
                                    -> void { _result = 1u; },
                                [&](const typename List<unsigned int>::Cons
                                        &_args0) -> void {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil &) -> void {
                                            _result = 2u;
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons &_args1)
                                              -> void {
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename List<
                                                        unsigned int>::Nil &)
                                                        -> void {
                                                      _result = 3u;
                                                    },
                                                    [&](const typename List<
                                                        unsigned int>::Cons
                                                            &_args2) -> void {
                                                      _stack.push_back(_Call1{
                                                          (((_args.d_a0 +
                                                             _args0.d_a0) +
                                                            _args1.d_a0) +
                                                           _args2.d_a0)});
                                                      _stack.push_back(
                                                          _Enter{_args2.d_a1});
                                                    }},
                                                _args1.d_a1->v());
                                          }},
                                      _args0.d_a1->v());
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::nested_pattern(
    const std::shared_ptr<
        List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<
        List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
        l;
  };

  struct _Call1 {
    decltype((
        (std::declval<unsigned int &>() + std::declval<unsigned int &>()) +
        std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::pair<
                  std::pair<unsigned int, unsigned int>, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<std::pair<unsigned int, unsigned int>,
                                    unsigned int>>::Nil &) -> void {
                        _result = 0u;
                      },
                      [&](const typename List<
                          std::pair<std::pair<unsigned int, unsigned int>,
                                    unsigned int>>::Cons &_args) -> void {
                        const std::pair<unsigned int, unsigned int> &p0 =
                            _args.d_a0.first;
                        const unsigned int &c = _args.d_a0.second;
                        const unsigned int &a = p0.first;
                        const unsigned int &b = p0.second;
                        _stack.push_back(_Call1{((a + b) + c)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::guard_accum(
    const unsigned int acc, const std::shared_ptr<List<unsigned int>> &l) {
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
                            if (100u < _args.d_a0) {
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  _args.d_a1;
                              unsigned int _next_acc = (_loop_acc * 2u);
                              _loop_l = std::move(_next_l);
                              _loop_acc = std::move(_next_acc);
                            } else {
                              if (50u < _args.d_a0) {
                                std::shared_ptr<List<unsigned int>> _next_l =
                                    _args.d_a1;
                                unsigned int _next_acc =
                                    (_loop_acc + _args.d_a0);
                                _loop_l = std::move(_next_l);
                                _loop_acc = std::move(_next_acc);
                              } else {
                                if (0u < _args.d_a0) {
                                  std::shared_ptr<List<unsigned int>> _next_l =
                                      _args.d_a1;
                                  unsigned int _next_acc = (_loop_acc + 1u);
                                  _loop_l = std::move(_next_l);
                                  _loop_acc = std::move(_next_acc);
                                } else {
                                  _loop_l = _args.d_a1;
                                }
                              }
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedPatterns::cons_computed(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
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
              unsigned int next_n;
              if (0u < _loop_n) {
                next_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
              } else {
                next_n = _loop_n;
              }
              auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_n = next_n;
              _loop_l = std::move(_next_l);
              _loop_n = std::move(_next_n);
            }},
        _loop_l->v());
  }
  return _head;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::extract_value(
    const std::shared_ptr<LoopifyAdvancedPatterns::shape> &s) {
  return std::visit(
      Overloaded{
          [](const typename LoopifyAdvancedPatterns::shape::Circle &_args)
              -> unsigned int { return _args.d_a0; },
          [](const typename LoopifyAdvancedPatterns::shape::Square &_args)
              -> unsigned int { return _args.d_a0; },
          [](const typename LoopifyAdvancedPatterns::shape::Triangle &_args)
              -> unsigned int { return _args.d_a0; }},
      s->v());
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::sum_shapes(
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        l;
  };

  struct _Call1 {
    decltype(extract_value(
        std::declval<const typename List<
            std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons
                              &_args) -> void {
                        _stack.push_back(_Call1{extract_value(_args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyAdvancedPatterns::count_by_shape(
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        l;
  };

  struct _Call1 {
    const typename List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons
        _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<std::shared_ptr<
                              LoopifyAdvancedPatterns::shape>>::Nil &) -> void {
                        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons
                              &_args) -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<
                  std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons _args =
                  _f._s0;
              const std::pair<unsigned int, unsigned int> &p = _result.first;
              const unsigned int &triangles = _result.second;
              const unsigned int &circles = p.first;
              const unsigned int &squares = p.second;
              _result = std::visit(
                  Overloaded{
                      [&](const typename LoopifyAdvancedPatterns::shape::Circle
                              &)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(
                            std::make_pair((circles + 1u), squares), triangles);
                      },
                      [&](const typename LoopifyAdvancedPatterns::shape::Square
                              &)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(
                            std::make_pair(circles, (squares + 1u)), triangles);
                      },
                      [&](const typename LoopifyAdvancedPatterns::shape::
                              Triangle &)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair(circles, squares),
                                              (triangles + 1u));
                      }},
                  _args.d_a0->v());
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedPatterns::replace_at(
    const unsigned int idx, const unsigned int value,
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
