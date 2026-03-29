#include <loopify_trees.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
__attribute__((pure)) unsigned int LoopifyTrees::tree_sum(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void { _result = 0u; },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
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
            [&](_Call2 _f) { _result = (_f._s1 + (_result + _f._s0)); }},
        _frame);
  }
  return _result;
}

/// leaf_sum sums only leaf values.
__attribute__((pure)) unsigned int LoopifyTrees::leaf_sum(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void { _result = 0u; },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyTrees::tree<
                                    unsigned int>::Leaf _args0) -> void {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename LoopifyTrees::tree<
                                              unsigned int>::Leaf _args1)
                                              -> void { _result = _args.d_a1; },
                                          [&](const typename LoopifyTrees::tree<
                                              unsigned int>::Node _args1)
                                              -> void {
                                            _stack.push_back(
                                                _Call1{_args.d_a0});
                                            _stack.push_back(
                                                _Enter{_args.d_a2});
                                          }},
                                      _args.d_a2->v());
                                },
                                [&](const typename LoopifyTrees::tree<
                                    unsigned int>::Node _args0) -> void {
                                  _stack.push_back(_Call3{_args.d_a0});
                                  _stack.push_back(_Enter{_args.d_a2});
                                }},
                            _args.d_a0->v());
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) { _result = (_result + _f._s0); }},
        _frame);
  }
  return _result;
}

/// insert_bst BST insertion.
std::shared_ptr<LoopifyTrees::tree<unsigned int>> LoopifyTrees::insert_bst(
    const unsigned int x,
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
    const unsigned int x;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a2) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyTrees::tree<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t, x});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              const unsigned int x = _f.x;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        _result = tree<unsigned int>::node(
                            tree<unsigned int>::leaf(), std::move(x),
                            tree<unsigned int>::leaf());
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        if (x <= _args.d_a1) {
                          _stack.push_back(_Call1{_args.d_a2, _args.d_a1});
                          _stack.push_back(_Enter{_args.d_a0, std::move(x)});
                        } else {
                          _stack.push_back(_Call2{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2, std::move(x)});
                        }
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _result = tree<unsigned int>::node(_result, _f._s1, _f._s0);
            },
            [&](_Call2 _f) {
              _result = tree<unsigned int>::node(_f._s1, _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// count_paths t n counts root-to-leaf paths that sum to n.
__attribute__((pure)) unsigned int LoopifyTrees::count_paths(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t,
    const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    decltype(0u) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    unsigned int _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s1;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int n = _f.n;
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        if (n == 0u) {
                          _result = 1u;
                        } else {
                          _result = 0u;
                        }
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        if (n <= _args.d_a1) {
                          if (n == _args.d_a1) {
                            _stack.push_back(_Call1{0u, _args.d_a0});
                            _stack.push_back(_Enter{0u, _args.d_a2});
                          } else {
                            _result = 0u;
                          }
                        } else {
                          unsigned int remaining =
                              (((n - _args.d_a1) > n ? 0 : (n - _args.d_a1)));
                          _stack.push_back(_Call3{remaining, _args.d_a0});
                          _stack.push_back(_Enter{remaining, _args.d_a2});
                        }
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call4 _f) { _result = (_result + _f._s0); }},
        _frame);
  }
  return _result;
}

/// sum_of_max_branches sums maximum values along each path.
__attribute__((pure)) unsigned int LoopifyTrees::sum_of_max_branches(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    const typename LoopifyTrees::tree<unsigned int>::Node _s0;
  };

  struct _Call2 {
    const typename LoopifyTrees::tree<unsigned int>::Node _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void { _result = 0u; },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyTrees::tree<unsigned int>::Node _args =
                  _f._s0;
              unsigned int lsum = _result;
              _stack.push_back(_Call2{_args, lsum});
              _stack.push_back(_Enter{_args.d_a2});
            },
            [&](_Call2 _f) {
              const typename LoopifyTrees::tree<unsigned int>::Node _args =
                  _f._s0;
              unsigned int lsum = _f._s1;
              unsigned int rsum = _result;
              _result = (_args.d_a1 + [&](void) {
                if (lsum <= rsum) {
                  return std::move(rsum);
                } else {
                  return std::move(lsum);
                }
              }());
            }},
        _frame);
  }
  return _result;
}

/// Helper: sum all values in a list of rose trees (processes both tree and
/// list levels in one recursive function to enable full loopification).
__attribute__((pure)) unsigned int LoopifyTrees::sum_rose_list_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>> &cs) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>> cs;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyTrees::rose::RNode &>()
                 .d_a1) _s0;
    unsigned int _s1;
    decltype(std::declval<const typename LoopifyTrees::rose::RNode &>()
                 .d_a0) _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(std::declval<const typename LoopifyTrees::rose::RNode &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{cs, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>>
                  cs = _f.cs;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = 0u;
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyTrees::rose>>::Nil _args)
                            -> void { _result = 0u; },
                        [&](const typename List<
                            std::shared_ptr<LoopifyTrees::rose>>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyTrees::rose::RNode
                                          _args0) -> void {
                                    _stack.push_back(
                                        _Call1{_args0.d_a1, f, _args0.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  }},
                              _args.d_a0->v());
                        }},
                    cs->v());
              }
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) { _result = (_f._s1 + (_result + _f._s0)); }},
        _frame);
  }
  return _result;
}

/// Helper: flatten a list of rose trees to a flat list of nats.
std::shared_ptr<List<unsigned int>> LoopifyTrees::flatten_rose_list_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>> &cs) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>> cs;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyTrees::rose::RNode &>()
                 .d_a1) _s0;
    unsigned int _s1;
    decltype(std::declval<const typename LoopifyTrees::rose::RNode &>()
                 .d_a0) _s2;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(std::declval<const typename LoopifyTrees::rose::RNode &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{cs, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>>
                  cs = _f.cs;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyTrees::rose>>::Nil _args)
                            -> void { _result = List<unsigned int>::nil(); },
                        [&](const typename List<
                            std::shared_ptr<LoopifyTrees::rose>>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyTrees::rose::RNode
                                          _args0) -> void {
                                    _stack.push_back(
                                        _Call1{_args0.d_a1, f, _args0.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  }},
                              _args.d_a0->v());
                        }},
                    cs->v());
              }
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) {
              _result = List<unsigned int>::cons(_f._s1, _result->app(_f._s0));
            }},
        _frame);
  }
  return _result;
}

/// Helper: compute maximum depth among a list of rose trees.
__attribute__((pure)) unsigned int LoopifyTrees::depth_rose_list_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>> &cs) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>> cs;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<std::shared_ptr<LoopifyTrees::rose>>::Cons _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{cs, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<LoopifyTrees::rose>>>
                  cs = _f.cs;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = 0u;
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyTrees::rose>>::Nil _args)
                            -> void { _result = 0u; },
                        [&](const typename List<
                            std::shared_ptr<LoopifyTrees::rose>>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyTrees::rose::RNode
                                          _args0) -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args0.d_a1, f});
                                  }},
                              _args.d_a0->v());
                        }},
                    cs->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<std::shared_ptr<LoopifyTrees::rose>>::Cons
                  _args = _f._s0;
              unsigned int f = _f._s1;
              unsigned int d = (_result + 1);
              _stack.push_back(_Call2{d});
              _stack.push_back(_Enter{_args.d_a1, f});
            },
            [&](_Call2 _f) {
              unsigned int d = _f._s0;
              unsigned int rest_max = _result;
              if (d <= rest_max) {
                _result = std::move(rest_max);
              } else {
                _result = std::move(d);
              }
            }},
        _frame);
  }
  return _result;
}

/// tree_max t1 t2 element-wise maximum of two trees.
std::shared_ptr<LoopifyTrees::tree<unsigned int>>
LoopifyTrees::tree_max(std::shared_ptr<LoopifyTrees::tree<unsigned int>> t1,
                       std::shared_ptr<LoopifyTrees::tree<unsigned int>> t2) {
  struct _Enter {
    std::shared_ptr<LoopifyTrees::tree<unsigned int>> t2;
    std::shared_ptr<LoopifyTrees::tree<unsigned int>> t1;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    std::shared_ptr<LoopifyTrees::tree<unsigned int>> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyTrees::tree<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyTrees::tree<unsigned int>> t2 = _f.t2;
              std::shared_ptr<LoopifyTrees::tree<unsigned int>> t1 = _f.t1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        if (t2.use_count() == 1 && t2->v().index() == 0) {
                          auto &_rf = std::get<0>(t2->v_mut());
                          _result = t2;
                        } else {
                          _result = std::visit(
                              Overloaded{
                                  [](const typename LoopifyTrees::tree<
                                      unsigned int>::Leaf _args0)
                                      -> std::shared_ptr<
                                          LoopifyTrees::tree<unsigned int>> {
                                    return tree<unsigned int>::leaf();
                                  },
                                  [&](const typename LoopifyTrees::tree<
                                      unsigned int>::Node _args0)
                                      -> std::shared_ptr<
                                          LoopifyTrees::tree<unsigned int>> {
                                    return std::move(t2);
                                  }},
                              t2->v());
                        }
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        std::visit(
                            Overloaded{[&](const typename LoopifyTrees::tree<
                                           unsigned int>::Leaf _args0) -> void {
                                         _result = std::move(t1);
                                       },
                                       [&](const typename LoopifyTrees::tree<
                                           unsigned int>::Node _args0) -> void {
                                         unsigned int max_val;
                                         if (_args.d_a1 <= _args0.d_a1) {
                                           max_val = _args0.d_a1;
                                         } else {
                                           max_val = _args.d_a1;
                                         }
                                         _stack.push_back(
                                             _Call1{_args0.d_a0, _args.d_a0,
                                                    std::move(max_val)});
                                         _stack.push_back(
                                             _Enter{_args0.d_a2, _args.d_a2});
                                       }},
                            std::move(t2)->v());
                      }},
                  t1->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) {
              _result = tree<unsigned int>::node(_result, _f._s1, _f._s0);
            }},
        _frame);
  }
  return _result;
}

/// Helper: extract values from trees.
std::shared_ptr<List<unsigned int>> LoopifyTrees::extract_tree_values(
    const std::shared_ptr<
        List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>> &ts) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
      _loop_ts = ts;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<
                std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<
                    LoopifyTrees::tree<unsigned int>>>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args0) { _loop_ts = _args.d_a1; },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args0.d_a1, nullptr);
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_ts = _args.d_a1;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ts->v());
  }
  return _head;
}

/// Helper: extract children from trees.
std::shared_ptr<List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
LoopifyTrees::extract_tree_children(
    const std::shared_ptr<
        List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>> &ts) {
  std::shared_ptr<List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
      _head{};
  std::shared_ptr<List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
      _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
      _loop_ts = ts;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<
                std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::Nil _args) {
              if (_last) {
                std::get<typename List<
                    std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = List<
                    std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::nil();
              } else {
                _head = List<
                    std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<
                    LoopifyTrees::tree<unsigned int>>>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args0) { _loop_ts = _args.d_a1; },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args0) {
                        auto _cell = List<std::shared_ptr<LoopifyTrees::tree<
                            unsigned int>>>::cons(_args0.d_a0, nullptr);
                        auto _cell1 = List<std::shared_ptr<LoopifyTrees::tree<
                            unsigned int>>>::cons(_args0.d_a2, nullptr);
                        std::get<typename List<std::shared_ptr<
                            LoopifyTrees::tree<unsigned int>>>::Cons>(
                            _cell->v_mut())
                            .d_a1 = _cell1;
                        if (_last) {
                          std::get<typename List<std::shared_ptr<
                              LoopifyTrees::tree<unsigned int>>>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell1;
                        _loop_ts = _args.d_a1;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ts->v());
  }
  return _head;
}

/// tree_levels t returns list of lists, one per level (breadth-first).
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTrees::tree_levels_fuel(
    const unsigned int fuel,
    const std::shared_ptr<
        List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>> &trees) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
      _loop_trees = trees;
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
      unsigned int f = _loop_fuel - 1;
      std::shared_ptr<List<unsigned int>> values =
          extract_tree_values(_loop_trees);
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
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
              [&](const typename List<unsigned int>::Cons _args) {
                std::shared_ptr<
                    List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
                    children = extract_tree_children(_loop_trees);
                auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                    std::move(values), nullptr);
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<
                    List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>>
                    _next_trees = std::move(children);
                unsigned int _next_fuel = f;
                _loop_trees = std::move(_next_trees);
                _loop_fuel = std::move(_next_fuel);
              }},
          values->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTrees::tree_levels(std::shared_ptr<LoopifyTrees::tree<unsigned int>> t) {
  return tree_levels_fuel(
      100u,
      List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::cons(
          std::move(t),
          List<std::shared_ptr<LoopifyTrees::tree<unsigned int>>>::nil()));
}

/// count_nodes t returns tuple (node_count, sum_of_values).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyTrees::count_nodes(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    const typename LoopifyTrees::tree<unsigned int>::Node _s0;
  };

  struct _Call2 {
    unsigned int _s0;
    const typename LoopifyTrees::tree<unsigned int>::Node _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        _result = std::make_pair(0u, 0u);
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyTrees::tree<unsigned int>::Node _args =
                  _f._s0;
              unsigned int lc = _result.first;
              unsigned int ls = _result.second;
              _stack.push_back(_Call2{ls, _args, lc});
              _stack.push_back(_Enter{_args.d_a2});
            },
            [&](_Call2 _f) {
              unsigned int ls = _f._s0;
              const typename LoopifyTrees::tree<unsigned int>::Node _args =
                  _f._s1;
              unsigned int lc = _f._s2;
              unsigned int rc = _result.first;
              unsigned int rs = _result.second;
              _result =
                  std::make_pair(((lc + rc) + 1), (_args.d_a1 + (ls + rs)));
            }},
        _frame);
  }
  return _result;
}

/// Helper: append two lists of lists.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTrees::append_list_lists(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &l1,
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> l2) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_l2 = l2;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_l1 = l1;
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
                    .d_a1 = std::move(_loop_l2);
              } else {
                _head = std::move(_loop_l2);
              }
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    _args) {
              auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                  _args.d_a0, nullptr);
              if (_last) {
                std::get<
                    typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  _next_l2 = std::move(_loop_l2);
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  _next_l1 = _args.d_a1;
              _loop_l2 = std::move(_next_l2);
              _loop_l1 = std::move(_next_l1);
            }},
        _loop_l1->v());
  }
  return _head;
}

/// Helper: prepend value to all lists in a list of lists.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTrees::map_cons_to_all(
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

/// paths t returns all root-to-leaf paths in tree.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> LoopifyTrees::paths(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s2;
  };

  struct _Call2 {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        _result =
                            List<std::shared_ptr<List<unsigned int>>>::cons(
                                List<unsigned int>::nil(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    nil());
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        _stack.push_back(
                            _Call1{_args.d_a0, _args.d_a1, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _result = append_list_lists(map_cons_to_all(_f._s2, _result),
                                          map_cons_to_all(_f._s1, _f._s0));
            }},
        _frame);
  }
  return _result;
}

/// collect_sorted t collects and sorts all tree values.
std::shared_ptr<List<unsigned int>> LoopifyTrees::collect_unsorted(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
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
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        _result = List<unsigned int>::nil();
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
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

/// Simple insertion sort for collect_sorted.
std::shared_ptr<List<unsigned int>>
LoopifyTrees::insert_sorted(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_x = x;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::cons(std::move(_loop_x),
                                                     List<unsigned int>::nil());
              } else {
                _head = List<unsigned int>::cons(std::move(_loop_x),
                                                 List<unsigned int>::nil());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (_loop_x <= _args.d_a0) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(
                      std::move(_loop_x),
                      List<unsigned int>::cons(_args.d_a0, _args.d_a1));
                } else {
                  _head = List<unsigned int>::cons(
                      std::move(_loop_x),
                      List<unsigned int>::cons(_args.d_a0, _args.d_a1));
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
                unsigned int _next_x = std::move(_loop_x);
                _loop_l = std::move(_next_l);
                _loop_x = std::move(_next_x);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyTrees::sort_list(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = insert_sorted(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyTrees::collect_sorted(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  return sort_list(collect_unsorted(t));
}

/// Helper: max of 4 values using nested max.
__attribute__((pure)) unsigned int
LoopifyTrees::max4_impl(const unsigned int a, const unsigned int b,
                        const unsigned int c, const unsigned int d) {
  if ([&](void) {
        if (a <= b) {
          return std::move(b);
        } else {
          return std::move(a);
        }
      }() <=
      [&](void) {
        if (c <= d) {
          return std::move(d);
        } else {
          return std::move(c);
        }
      }()) {
    if (c <= d) {
      return std::move(d);
    } else {
      return std::move(c);
    }
  } else {
    if (a <= b) {
      return std::move(b);
    } else {
      return std::move(a);
    }
  }
}

/// Helper: compute minimum of three values.
__attribute__((pure)) unsigned int LoopifyTrees::min3(const unsigned int a,
                                                      const unsigned int b,
                                                      const unsigned int c) {
  if (a <= b) {
    if (a <= c) {
      return std::move(a);
    } else {
      return std::move(c);
    }
  } else {
    if (b <= c) {
      return std::move(b);
    } else {
      return std::move(c);
    }
  }
}

/// Helper: compute maximum of three values.
__attribute__((pure)) unsigned int LoopifyTrees::max3(const unsigned int a,
                                                      const unsigned int b,
                                                      const unsigned int c) {
  if (b <= a) {
    if (c <= a) {
      return std::move(a);
    } else {
      return std::move(c);
    }
  } else {
    if (c <= b) {
      return std::move(b);
    } else {
      return std::move(c);
    }
  }
}

/// tree_min_max t finds minimum and maximum values in tree.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyTrees::tree_min_max(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    const typename LoopifyTrees::tree<unsigned int>::Node _s0;
  };

  struct _Call2 {
    const typename LoopifyTrees::tree<unsigned int>::Node _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void {
                        _result = std::make_pair(0u, 0u);
                      },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyTrees::tree<unsigned int>::Node _args =
                  _f._s0;
              unsigned int lmin = _result.first;
              unsigned int lmax = _result.second;
              _stack.push_back(_Call2{_args, lmax, lmin});
              _stack.push_back(_Enter{_args.d_a2});
            },
            [&](_Call2 _f) {
              const typename LoopifyTrees::tree<unsigned int>::Node _args =
                  _f._s0;
              unsigned int lmax = _f._s1;
              unsigned int lmin = _f._s2;
              unsigned int rmin = _result.first;
              unsigned int rmax = _result.second;
              _result = std::make_pair(min3(
                                           [&](void) {
                                             if (lmin == 0u) {
                                               return _args.d_a1;
                                             } else {
                                               return lmin;
                                             }
                                           }(),
                                           [&](void) {
                                             if (rmin == 0u) {
                                               return _args.d_a1;
                                             } else {
                                               return rmin;
                                             }
                                           }(),
                                           _args.d_a1),
                                       max3(lmax, rmax, _args.d_a1));
            }},
        _frame);
  }
  return _result;
}

/// all_paths_sum t sums all root-to-leaf path sums.
__attribute__((pure)) unsigned int LoopifyTrees::all_paths_sum(
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  std::function<unsigned int(unsigned int,
                             std::shared_ptr<LoopifyTrees::tree<unsigned int>>)>
      sum_with_acc;
  sum_with_acc = [&](unsigned int acc,
                     std::shared_ptr<LoopifyTrees::tree<unsigned int>> tree0)
      -> unsigned int {
    struct _Enter {
      std::shared_ptr<LoopifyTrees::tree<unsigned int>> tree0;
      unsigned int acc;
    };
    struct _Call1 {
      decltype(std::declval<
                   const typename LoopifyTrees::tree<unsigned int>::Node &>()
                   .d_a0) _s0;
      unsigned int _s1;
    };
    struct _Call2 {
      unsigned int _s0;
    };
    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{tree0, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<LoopifyTrees::tree<unsigned int>> tree0 =
                           _f.tree0;
                       unsigned int acc = _f.acc;
                       std::visit(
                           Overloaded{
                               [&](const typename LoopifyTrees::tree<
                                   unsigned int>::Leaf _args) -> void {
                                 _result = std::move(acc);
                               },
                               [&](const typename LoopifyTrees::tree<
                                   unsigned int>::Node _args) -> void {
                                 unsigned int new_acc =
                                     (std::move(acc) + _args.d_a1);
                                 _stack.push_back(_Call1{_args.d_a0, new_acc});
                                 _stack.push_back(_Enter{_args.d_a2, new_acc});
                               }},
                           tree0->v());
                     },
                     [&](_Call1 _f) {
                       _stack.push_back(_Call2{_result});
                       _stack.push_back(_Enter{_f._s0, _f._s1});
                     },
                     [&](_Call2 _f) { _result = (_result + _f._s0); }},
          _frame);
    }
    return _result;
  };
  return sum_with_acc(0u, t);
}

/// tree_contains x t checks if value exists in tree.
__attribute__((pure)) bool LoopifyTrees::tree_contains(
    const unsigned int x,
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    bool _s0;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<
                 const typename LoopifyTrees::tree<unsigned int>::Node &>()
                 .d_a1) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTrees::tree<unsigned int>> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTrees::tree<unsigned int>::Leaf
                              _args) -> void { _result = false; },
                      [&](const typename LoopifyTrees::tree<unsigned int>::Node
                              _args) -> void {
                        _stack.push_back(_Call1{_args.d_a0, x == _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_f._s1 || (_result || _f._s0)); }},
        _frame);
  }
  return _result;
}
