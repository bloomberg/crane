#include <loopify_more_trees.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> std::shared_ptr<LoopifyMoreTrees::tree> {
                        _result = tree::ctor::Leaf_();
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> std::shared_ptr<LoopifyMoreTrees::tree> {
                        _stack.push_back(_Call1{_args.d_a2, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _result = tree::ctor::Node_(_result, _f._s1, _f._s0);
            }},
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
  _stack.push_back(_Enter{t2, t1});
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
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> bool {
                        _result = std::visit(
                            Overloaded{
                                [](const typename LoopifyMoreTrees::tree::Leaf
                                       _args0) -> bool { return true; },
                                [](const typename LoopifyMoreTrees::tree::Node
                                       _args0) -> bool { return false; }},
                            t2->v());
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> bool {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyMoreTrees::tree::Leaf
                                        _args0) -> bool {
                                  _result = false;
                                  return {};
                                },
                                [&](const typename LoopifyMoreTrees::tree::Node
                                        _args0) -> bool {
                                  _stack.push_back(
                                      _Call1{_args0.d_a0, _args.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a2, _args.d_a2});
                                  return {};
                                }},
                            t2->v());
                        return {};
                      }},
                  t1->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
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
    decltype(List<unsigned int>::ctor::Cons_(
        std::declval<const typename LoopifyMoreTrees::tree::Node &>().d_a1,
        List<unsigned int>::ctor::Nil_())) _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(List<unsigned int>::ctor::Cons_(
        std::declval<const typename LoopifyMoreTrees::tree::Node &>().d_a1,
        List<unsigned int>::ctor::Nil_())) _s1;
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
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _stack.push_back(_Call1{
                            _args.d_a0,
                            List<unsigned int>::ctor::Cons_(
                                _args.d_a1, List<unsigned int>::ctor::Nil_())});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
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
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
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
  _stack.push_back(_Enter{t2, t1});
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
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> std::shared_ptr<LoopifyMoreTrees::tree> {
                        _result = std::move(t2);
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> std::shared_ptr<LoopifyMoreTrees::tree> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyMoreTrees::tree::Leaf
                                        _args0)
                                    -> std::shared_ptr<LoopifyMoreTrees::tree> {
                                  _result = std::move(t1);
                                  return {};
                                },
                                [&](const typename LoopifyMoreTrees::tree::Node
                                        _args0)
                                    -> std::shared_ptr<LoopifyMoreTrees::tree> {
                                  _stack.push_back(_Call1{
                                      _args0.d_a0, _args.d_a0,
                                      std::max(_args.d_a1, _args0.d_a1)});
                                  _stack.push_back(
                                      _Enter{_args0.d_a2, _args.d_a2});
                                  return {};
                                }},
                            std::move(t2)->v());
                        return {};
                      }},
                  t1->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) {
              _result = tree::ctor::Node_(_result, _f._s1, _f._s0);
            }},
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
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
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
    const unsigned int x;
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
  _stack.push_back(_Enter{t, x});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMoreTrees::tree> t = _f.t;
              const unsigned int x = _f.x;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMoreTrees::tree::Leaf _args)
                          -> std::shared_ptr<LoopifyMoreTrees::tree> {
                        _result =
                            tree::ctor::Node_(tree::ctor::Leaf_(), std::move(x),
                                              tree::ctor::Leaf_());
                        return {};
                      },
                      [&](const typename LoopifyMoreTrees::tree::Node _args)
                          -> std::shared_ptr<LoopifyMoreTrees::tree> {
                        if (x <= _args.d_a1) {
                          _stack.push_back(_Call1{_args.d_a2, _args.d_a1});
                          _stack.push_back(_Enter{_args.d_a0, std::move(x)});
                        } else {
                          _stack.push_back(_Call2{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2, std::move(x)});
                        }
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _result = tree::ctor::Node_(_result, _f._s1, _f._s0);
            },
            [&](_Call2 _f) {
              _result = tree::ctor::Node_(_f._s1, _f._s0, _result);
            }},
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
                                 -> std::shared_ptr<LoopifyMoreTrees::tree> {
                               _result = tree::ctor::Leaf_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<LoopifyMoreTrees::tree> {
                               _stack.push_back(_Call1{_args.d_a0});
                               _stack.push_back(_Enter{_args.d_a1});
                               return {};
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
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     std::shared_ptr<List<unsigned int>> l2 = _f.l2;
                     const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = std::move(l2);
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _stack.push_back(_Call1{_args.d_a0});
                               _stack.push_back(
                                   _Enter{std::move(l2), _args.d_a1});
                               return {};
                             }},
                         l1->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
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
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
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
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> lt;
  };

  struct _Call1 {
    decltype(tree_to_list(
        std::declval<const typename List<
            std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{lt});
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
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _result = List<
                            std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _stack.push_back(_Call1{tree_to_list(_args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  lt->v());
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::tree_children(
    const std::shared_ptr<LoopifyMoreTrees::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename LoopifyMoreTrees::tree::Leaf _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
            return List<std::shared_ptr<LoopifyMoreTrees::tree>>::ctor::Nil_();
          },
          [](const typename LoopifyMoreTrees::tree::Node _args)
              -> std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
            return List<std::shared_ptr<LoopifyMoreTrees::tree>>::ctor::Cons_(
                _args.d_a0,
                List<std::shared_ptr<LoopifyMoreTrees::tree>>::ctor::Cons_(
                    _args.d_a2, List<std::shared_ptr<LoopifyMoreTrees::tree>>::
                                    ctor::Nil_()));
          }},
      t->v());
}

std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
LoopifyMoreTrees::append_trees(
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> &l1,
    std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> l2) {
  struct _Enter {
    std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> l2;
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<LoopifyMoreTrees::tree>>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                  l2 = _f.l2;
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                  l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
                        _result = std::move(l2);
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result =
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>::ctor::Cons_(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
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
  _stack.push_back(_Enter{lt});
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
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
                        _result =
                            List<std::shared_ptr<LoopifyMoreTrees::tree>>::
                                ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyMoreTrees::tree>>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<LoopifyMoreTrees::tree>>> {
                        _stack.push_back(_Call1{tree_children(_args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
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
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyMoreTrees::tree>>> level;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{level, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                  level = _f.level;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyMoreTrees::tree>>::Nil _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<std::shared_ptr<
                                LoopifyMoreTrees::tree>>::Cons _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          std::shared_ptr<List<unsigned int>> values =
                              flatten(map_tree_to_list(level));
                          std::shared_ptr<
                              List<std::shared_ptr<LoopifyMoreTrees::tree>>>
                              next = concat_map_children(level);
                          _stack.push_back(_Call1{std::move(values)});
                          _stack.push_back(_Enter{std::move(next), fuel_});
                          return {};
                        }},
                    level->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyMoreTrees::tree_levels(std::shared_ptr<LoopifyMoreTrees::tree> t) {
  return tree_levels_fuel(
      100u, List<std::shared_ptr<LoopifyMoreTrees::tree>>::ctor::Cons_(
                std::move(t),
                List<std::shared_ptr<LoopifyMoreTrees::tree>>::ctor::Nil_()));
}
