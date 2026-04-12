#include <loopify_more_trees.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::mirror(const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a2) _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a1) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void { _result = tree::leaf(); },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        _stack.emplace_back(_Call1{_args.d_a2, _args.d_a1});
                        _stack.emplace_back(_Enter{_args.d_a0});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.emplace_back(_Call2{_result, _f._s1});
              _stack.emplace_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = tree::node(_result, _f._s1, _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyMoreTrees::same_shape(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t1,
    const std::shared_ptr<LoopifyMoreTrees::tree> &t2) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t2;
    const std::shared_ptr<LoopifyMoreTrees::tree> t1;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s1;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t2 = _f.t2;
              const std::shared_ptr<LoopifyMoreTrees::tree> t1 = _f.t1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void {
                        _result = std::visit(
                            Overloaded{
                                [](const typename LoopifyMoreTrees::tree::Leaf
                                       &) -> bool { return true; },
                                [](const typename LoopifyMoreTrees::tree::Node
                                       &) -> bool { return false; }},
                            t2->v());
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyMoreTrees::tree::Leaf
                                        &) -> void { _result = false; },
                                [&](const typename LoopifyMoreTrees::tree::Node
                                        &_args0) -> void {
                                  _stack.emplace_back(
                                      _Call1{_args0.d_a0, _args.d_a0});
                                  _stack.emplace_back(
                                      _Enter{_args0.d_a2, _args.d_a2});
                                }},
                            t2->v());
                      }},
                  t1->v());
            },
            [&](_Call1 _f) {
              _stack.emplace_back(_Call2{_result});
              _stack.emplace_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) { _result = (_result && _f._s0); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyMoreTrees::tree_to_list(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s0;
    decltype(List<unsigned int>::cons(
        std::declval<const typename LoopifyMoreTrees::tree::Node &>().d_a1,
        List<unsigned int>::nil())) _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(List<unsigned int>::cons(
        std::declval<const typename LoopifyMoreTrees::tree::Node &>().d_a1,
        List<unsigned int>::nil())) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        _stack.emplace_back(
                            _Call1{_args.d_a0,
                                   List<unsigned int>::cons(
                                       _args.d_a1, List<unsigned int>::nil())});
                        _stack.emplace_back(_Enter{_args.d_a2});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.emplace_back(_Call2{_result, _f._s1});
              _stack.emplace_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = _result->app(_f._s1->app(_f._s0)); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyMoreTrees::mirror_equal(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  return same_shape(t, mirror(t));
}

__attribute__((pure)) unsigned int LoopifyMoreTrees::count_nodes(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s0;
    decltype(1u) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(1u) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void { _result = 0u; },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        _stack.emplace_back(_Call1{_args.d_a0, 1u});
                        _stack.emplace_back(_Enter{_args.d_a2});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.emplace_back(_Call2{_result, _f._s1});
              _stack.emplace_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = ((_f._s1 + _result) + _f._s0); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::tree_max(std::shared_ptr<LoopifyMoreTrees::tree> t1,
                           std::shared_ptr<LoopifyMoreTrees::tree> t2) {
  struct _Enter {
    std::shared_ptr<LoopifyMoreTrees::tree> t2;
    std::shared_ptr<LoopifyMoreTrees::tree> t1;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s1;
    decltype(std::max(
        std::declval<const typename LoopifyMoreTrees::tree::Node &>().d_a1,
        std::declval<const typename LoopifyMoreTrees::tree::Node &>()
            .d_a1)) _s2;
  };

  struct _Call2 {
    std::shared_ptr<LoopifyMoreTrees::tree> _s0;
    decltype(std::max(
        std::declval<const typename LoopifyMoreTrees::tree::Node &>().d_a1,
        std::declval<const typename LoopifyMoreTrees::tree::Node &>()
            .d_a1)) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyMoreTrees::tree> t2 = _f.t2;
              std::shared_ptr<LoopifyMoreTrees::tree> t1 = _f.t1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void { _result = std::move(t2); },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyMoreTrees::tree::Leaf
                                        &) -> void { _result = std::move(t1); },
                                [&](const typename LoopifyMoreTrees::tree::Node
                                        &_args0) -> void {
                                  _stack.emplace_back(_Call1{
                                      _args0.d_a0, _args.d_a0,
                                      std::max(_args.d_a1, _args0.d_a1)});
                                  _stack.emplace_back(
                                      _Enter{_args0.d_a2, _args.d_a2});
                                }},
                            t2->v());
                      }},
                  t1->v());
            },
            [&](_Call1 _f) {
              _stack.emplace_back(_Call2{_result, _f._s2});
              _stack.emplace_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) { _result = tree::node(_result, _f._s1, _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyMoreTrees::sum_of_max_branches(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a1) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void { _result = 0u; },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        _stack.emplace_back(_Call1{_args.d_a0, _args.d_a1});
                        _stack.emplace_back(_Enter{_args.d_a2});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.emplace_back(_Call2{_result, _f._s1});
              _stack.emplace_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_f._s1 + std::max(_result, _f._s0)); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::insert_bst(const unsigned int x,
                             const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMoreTrees::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a2) _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a1) _s0;
    decltype(std::declval<const typename LoopifyMoreTrees::tree::Node &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf &)
                          -> void {
                        _result = tree::node(tree::leaf(), x, tree::leaf());
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node &_args)
                          -> void {
                        if (x <= _args.d_a1) {
                          _stack.emplace_back(_Call1{_args.d_a2, _args.d_a1});
                          _stack.emplace_back(_Enter{_args.d_a0});
                        } else {
                          _stack.emplace_back(_Call2{_args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a2});
                        }
                      }},
                  t->v());
            },
            [&](_Call1 _f) { _result = tree::node(_result, _f._s1, _f._s0); },
            [&](_Call2 _f) { _result = tree::node(_f._s1, _f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<LoopifyMoreTrees::tree>
LoopifyMoreTrees::build_bst(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyMoreTrees::tree> _result{};
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
                                 -> void { _result = tree::leaf(); },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
                               _stack.emplace_back(_Call1{_args.d_a0});
                               _stack.emplace_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = insert_bst(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyMoreTrees::append_lists(const std::shared_ptr<List<unsigned int>> &l1,
                               std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(l2);
              } else {
                _head = std::move(l2);
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
              _loop_l1 = _args.d_a1;
            }},
        _loop_l1->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyMoreTrees::flatten(
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
            [&](_Call1 _f) { _result = append_lists(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::map_tree_to_list(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &lt) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _loop_lt = lt;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<
                std::shared_ptr<LoopifyMoreTrees::tree>>::Nil &) {
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
            [&](const typename List<
                std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &_args) {
              auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                  tree_to_list(_args.d_a0), nullptr);
              if (_last) {
                std::get<
                    typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                    _last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              _loop_lt = _args.d_a1;
            }},
        _loop_lt->v());
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::tree_children(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename LoopifyMoreTrees::tree::Leaf &)
              -> std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
            return List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil();
          },
          [](const typename LoopifyMoreTrees::tree::Node &_args)
              -> std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
            return List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
                _args.d_a0,
                List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
                    _args.d_a2,
                    List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil()));
          }},
      t->v());
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::append_trees(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &l1,
    std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> l2) {
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _head{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<
                       std::shared_ptr<LoopifyMoreTrees::tree>>::Nil &) {
                     if (_last) {
                       std::get<typename List<
                           std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
                           _last->v_mut())
                           .d_a1 = std::move(l2);
                     } else {
                       _head = std::move(l2);
                     }
                     _continue = false;
                   },
                   [&](const typename List<
                       std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &_args) {
                     auto _cell =
                         List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
                             _args.d_a0, nullptr);
                     if (_last) {
                       std::get<typename List<
                           std::shared_ptr<LoopifyMoreTrees::tree>>::Cons>(
                           _last->v_mut())
                           .d_a1 = _cell;
                     } else {
                       _head = _cell;
                     }
                     _last = _cell;
                     _loop_l1 = _args.d_a1;
                   }},
        _loop_l1->v());
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::concat_map_children(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &lt) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> lt;
  };

  struct _Call1 {
    decltype(tree_children(
        std::declval<const typename List<
            std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{lt});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                  lt = _f.lt;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Nil &)
                          -> void {
                        _result = List<
                            std::shared_ptr<LoopifyMoreTrees::tree>>::nil();
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{tree_children(_args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  lt->v());
            },
            [&](_Call1 _f) { _result = append_trees(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::tree_levels_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
        &level) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _loop_level =
      level;
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
              [&](const typename List<
                  std::shared_ptr<LoopifyMoreTrees::tree>>::Nil &) {
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
              [&](const typename List<
                  std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &) {
                std::shared_ptr<List<unsigned int>> values =
                    flatten(map_tree_to_list(_loop_level));
                std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                    next = concat_map_children(_loop_level);
                auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                    values, nullptr);
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                    _next_level = next;
                unsigned int _next_fuel = fuel_;
                _loop_level = std::move(_next_level);
                _loop_fuel = std::move(_next_fuel);
              }},
          _loop_level->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::tree_levels(std::shared_ptr<LoopifyMoreTrees::tree> t) {
  return tree_levels_fuel(
      100u, List<std::shared_ptr<LoopifyMoreTrees::tree>>::cons(
                t, List<std::shared_ptr<LoopifyMoreTrees::tree>>::nil()));
}
