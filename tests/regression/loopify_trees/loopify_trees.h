#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
      std::shared_ptr<List<t_A>> m;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<t_A>::Cons &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<t_A>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{_self, m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const List *_self = _f._self;
                std::shared_ptr<List<t_A>> m = _f.m;
                std::visit(
                    Overloaded{
                        [&](const typename List<t_A>::Nil _args) -> void {
                          _result = m;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{m.get(), _args.d_a1});
                        }},
                    _self->v());
              },
              [&](_Call1 _f) {
                _result = List<t_A>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }
};

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
struct LoopifyTrees {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::shared_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree<t_A>> Leaf_() {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Leaf{}));
      }

      static std::shared_ptr<tree<t_A>>
      Node_(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
            const std::shared_ptr<tree<t_A>> &a2) {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Node{a0, a1, a2}));
      }

      static std::unique_ptr<tree<t_A>> Leaf_uptr() {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Leaf{}));
      }

      static std::unique_ptr<tree<t_A>>
      Node_uptr(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
                const std::shared_ptr<tree<t_A>> &a2) {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Node{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rect(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = f;
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                  _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = f;
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                  _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree<unsigned int>> &t);

  template <typename T1>
  __attribute__((pure)) static unsigned int
  tree_height(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      const typename tree<T1>::Node _s0;
    };

    struct _Call2 {
      unsigned int _s0;
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
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = 0u;
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args});
                          _stack.push_back(_Enter{_args.d_a0});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                const typename tree<T1>::Node _args = _f._s0;
                unsigned int lh = _result;
                _stack.push_back(_Call2{lh});
                _stack.push_back(_Enter{_args.d_a2});
              },
              [&](_Call2 _f) {
                unsigned int lh = _f._s0;
                unsigned int rh = _result;
                _result = ([&](void) {
                  if (lh <= rh) {
                    return std::move(rh);
                  } else {
                    return std::move(lh);
                  }
                }() + 1);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
    };

    struct _Call2 {
      unsigned int _s0;
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
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = 0u;
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = ((_result + _f._s0) + 1); }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<tree<T1>> mirror(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s1;
    };

    struct _Call2 {
      std::shared_ptr<tree<T1>> _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<tree<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = tree<T1>::ctor::Leaf_();
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args.d_a2, _args.d_a1});
                          _stack.push_back(_Enter{_args.d_a0});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = tree<T1>::ctor::Node_(_result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  } /// same_shape tests structural equality.

  template <typename T1, typename T2>
  __attribute__((pure)) static bool
  same_shape(const std::shared_ptr<tree<T1>> &t1,
             const std::shared_ptr<tree<T2>> &t2) {
    struct _Enter {
      const std::shared_ptr<tree<T2>> t2;
      const std::shared_ptr<tree<T1>> t1;
    };

    struct _Call1 {
      const typename tree<T2>::Node _s0;
      const typename tree<T1>::Node _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t2, t1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T2>> t2 = _f.t2;
                const std::shared_ptr<tree<T1>> t1 = _f.t1;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = std::visit(
                              Overloaded{
                                  [](const typename tree<T2>::Leaf _args0)
                                      -> bool { return true; },
                                  [](const typename tree<T2>::Node _args0)
                                      -> bool { return false; }},
                              t2->v());
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename tree<T2>::Leaf _args0)
                                      -> void { _result = false; },
                                  [&](const typename tree<T2>::Node _args0)
                                      -> void {
                                    _stack.push_back(_Call1{_args0, _args});
                                    _stack.push_back(
                                        _Enter{_args0.d_a0, _args.d_a0});
                                  }},
                              t2->v());
                        }},
                    t1->v());
              },
              [&](_Call1 _f) {
                const typename tree<T2>::Node _args0 = _f._s0;
                const typename tree<T1>::Node _args = _f._s1;
                if (_result) {
                  _stack.push_back(_Enter{_args0.d_a2, _args.d_a2});
                } else {
                  _result = false;
                }
              }},
          _frame);
    }
    return _result;
  } /// leftmost/rightmost finds edge values.

  template <typename T1>
  static T1 leftmost(const T1 default0, const std::shared_ptr<tree<T1>> &t) {
    T1 _result;
    std::shared_ptr<tree<T1>> _loop_t = t;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{[&](const typename tree<T1>::Leaf _args) {
                       _result = default0;
                       _continue = false;
                     },
                     [&](const typename tree<T1>::Node _args) {
                       std::visit(
                           Overloaded{
                               [&](const typename tree<T1>::Leaf _args0) {
                                 _result = _args.d_a1;
                                 _continue = false;
                               },
                               [&](const typename tree<T1>::Node _args0) {
                                 _loop_t = _args.d_a0;
                               }},
                           _args.d_a0->v());
                     }},
          _loop_t->v());
    }
    return _result;
  }

  template <typename T1>
  static T1 rightmost(const T1 default0, const std::shared_ptr<tree<T1>> &t) {
    T1 _result;
    std::shared_ptr<tree<T1>> _loop_t = t;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{[&](const typename tree<T1>::Leaf _args) {
                       _result = default0;
                       _continue = false;
                     },
                     [&](const typename tree<T1>::Node _args) {
                       std::visit(
                           Overloaded{
                               [&](const typename tree<T1>::Leaf _args0) {
                                 _result = _args.d_a1;
                                 _continue = false;
                               },
                               [&](const typename tree<T1>::Node _args0) {
                                 _loop_t = _args.d_a2;
                               }},
                           _args.d_a2->v());
                     }},
          _loop_t->v());
    }
    return _result;
  } /// count_leaves counts leaf nodes.

  template <typename T1>
  __attribute__((pure)) static unsigned int
  count_leaves(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
    };

    struct _Call2 {
      unsigned int _s0;
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
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = 1u;
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = (_result + _f._s0); }},
          _frame);
    }
    return _result;
  }

  /// leaf_sum sums only leaf values.
  __attribute__((pure)) static unsigned int
  leaf_sum(const std::shared_ptr<tree<unsigned int>> &t);
  /// insert_bst BST insertion.
  static std::shared_ptr<tree<unsigned int>>
  insert_bst(const unsigned int x,
             const std::shared_ptr<tree<unsigned int>> &t);

  /// tree_to_list inorder traversal.
  template <typename T1>
  static std::shared_ptr<List<T1>>
  tree_to_list(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s1;
    };

    struct _Call2 {
      std::shared_ptr<List<T1>> _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = List<T1>::ctor::Nil_();
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
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
                _result = _result->app(List<T1>::ctor::Cons_(_f._s1, _f._s0));
              }},
          _frame);
    }
    return _result;
  }

  /// count_paths t n counts root-to-leaf paths that sum to n.
  __attribute__((pure)) static unsigned int
  count_paths(const std::shared_ptr<tree<unsigned int>> &t,
              const unsigned int n);
  /// sum_of_max_branches sums maximum values along each path.
  __attribute__((pure)) static unsigned int
  sum_of_max_branches(const std::shared_ptr<tree<unsigned int>> &t);

  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> d_a0;
      std::shared_ptr<ternary> d_a1;
      std::shared_ptr<ternary> d_a2;
      unsigned int d_a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit ternary(TLeaf _v) : d_v_(std::move(_v)) {}

    explicit ternary(TNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<ternary> TLeaf_() {
        return std::shared_ptr<ternary>(new ternary(TLeaf{}));
      }

      static std::shared_ptr<ternary> TNode_(const std::shared_ptr<ternary> &a0,
                                             const std::shared_ptr<ternary> &a1,
                                             const std::shared_ptr<ternary> &a2,
                                             unsigned int a3) {
        return std::shared_ptr<ternary>(new ternary(TNode{a0, a1, a2, a3}));
      }

      static std::unique_ptr<ternary> TLeaf_uptr() {
        return std::unique_ptr<ternary>(new ternary(TLeaf{}));
      }

      static std::unique_ptr<ternary>
      TNode_uptr(const std::shared_ptr<ternary> &a0,
                 const std::shared_ptr<ternary> &a1,
                 const std::shared_ptr<ternary> &a2, unsigned int a3) {
        return std::unique_ptr<ternary>(new ternary(TNode{a0, a1, a2, a3}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<ternary>, T1, std::shared_ptr<ternary>,
                   T1, std::shared_ptr<ternary>, T1, unsigned int>
                F1>
  static T1 ternary_rect(const T1 f, F1 &&f0,
                         const std::shared_ptr<ternary> &t) {
    struct _Enter {
      const std::shared_ptr<ternary> t;
    };

    struct _Call1 {
      const std::shared_ptr<ternary> _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<ternary> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename ternary::TLeaf _args) -> void {
                          _result = f;
                        },
                        [&](const typename ternary::TNode _args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0,
                                                  _args.d_a3, _args.d_a2,
                                                  _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(
                    _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.push_back(
                    _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _result =
                    f0(_f._s5, _result, _f._s4, _f._s1, _f._s3, _f._s0, _f._s2);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<ternary>, T1, std::shared_ptr<ternary>,
                   T1, std::shared_ptr<ternary>, T1, unsigned int>
                F1>
  static T1 ternary_rec(const T1 f, F1 &&f0,
                        const std::shared_ptr<ternary> &t) {
    struct _Enter {
      const std::shared_ptr<ternary> t;
    };

    struct _Call1 {
      const std::shared_ptr<ternary> _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<ternary> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename ternary::TLeaf _args) -> void {
                          _result = f;
                        },
                        [&](const typename ternary::TNode _args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0,
                                                  _args.d_a3, _args.d_a2,
                                                  _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(
                    _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.push_back(
                    _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _result =
                    f0(_f._s5, _result, _f._s4, _f._s1, _f._s3, _f._s0, _f._s2);
              }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  ternary_sum(const std::shared_ptr<ternary> &t);
  __attribute__((pure)) static unsigned int
  ternary_depth(const std::shared_ptr<ternary>
                    &t); /// Rose tree: a tree with variable number of children.

  struct rose {
    // TYPES
    struct RNode {
      unsigned int d_a0;
      std::shared_ptr<List<std::shared_ptr<rose>>> d_a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit rose(RNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<rose>
      RNode_(unsigned int a0,
             const std::shared_ptr<List<std::shared_ptr<rose>>> &a1) {
        return std::shared_ptr<rose>(new rose(RNode{a0, a1}));
      }

      static std::unique_ptr<rose>
      RNode_uptr(unsigned int a0,
                 const std::shared_ptr<List<std::shared_ptr<rose>>> &a1) {
        return std::unique_ptr<rose>(new rose(RNode{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<List<std::shared_ptr<rose>>>> F0>
  static T1 rose_rect(F0 &&f, const std::shared_ptr<rose> &r) {
    return std::visit(Overloaded{[&](const typename rose::RNode _args) -> T1 {
                        return f(_args.d_a0, _args.d_a1);
                      }},
                      r->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<List<std::shared_ptr<rose>>>> F0>
  static T1 rose_rec(F0 &&f, const std::shared_ptr<rose> &r) {
    return std::visit(Overloaded{[&](const typename rose::RNode _args) -> T1 {
                        return f(_args.d_a0, _args.d_a1);
                      }},
                      r->v());
  }

  /// Helper: sum all values in a list of rose trees (processes both tree and
  /// list levels in one recursive function to enable full loopification).
  __attribute__((pure)) static unsigned int
  sum_rose_list_fuel(const unsigned int fuel,
                     const std::shared_ptr<List<std::shared_ptr<rose>>> &cs);
  /// rose_sum t sums all values in a rose tree.
  __attribute__((pure)) static unsigned int
  rose_sum(const std::shared_ptr<rose> &t);

  /// Helper: map function over all values in a list of rose trees.
  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<std::shared_ptr<rose>>>
  map_rose_list_fuel(const unsigned int fuel, F1 &&f,
                     const std::shared_ptr<List<std::shared_ptr<rose>>> &cs) {
    struct _Enter {
      const std::shared_ptr<List<std::shared_ptr<rose>>> cs;
      const unsigned int fuel;
    };

    struct _Call1 {
      decltype(std::declval<const typename rose::RNode &>().d_a1) _s0;
      unsigned int _s1;
      unsigned int _s2;
    };

    struct _Call2 {
      std::shared_ptr<List<std::shared_ptr<rose>>> _s0;
      unsigned int _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<List<std::shared_ptr<rose>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{cs, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<std::shared_ptr<rose>>> cs = _f.cs;
                const unsigned int fuel = _f.fuel;
                if (fuel <= 0) {
                  _result = List<std::shared_ptr<rose>>::ctor::Nil_();
                } else {
                  unsigned int g = fuel - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename List<std::shared_ptr<rose>>::Nil
                                  _args) -> void {
                            _result = List<std::shared_ptr<rose>>::ctor::Nil_();
                          },
                          [&](const typename List<std::shared_ptr<rose>>::Cons
                                  _args) -> void {
                            std::visit(
                                Overloaded{
                                    [&](const typename rose::RNode _args0)
                                        -> void {
                                      _stack.push_back(_Call1{_args0.d_a1, g,
                                                              f(_args0.d_a0)});
                                      _stack.push_back(_Enter{_args.d_a1, g});
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
                _result = List<std::shared_ptr<rose>>::ctor::Cons_(
                    rose::ctor::RNode_(_f._s1, _result), _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// rose_map f t applies f to all values in a rose tree.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<rose> rose_map(F0 &&f,
                                        const std::shared_ptr<rose> &t) {
    return std::visit(
        Overloaded{
            [&](const typename rose::RNode _args) -> std::shared_ptr<rose> {
              return rose::ctor::RNode_(
                  f(_args.d_a0), map_rose_list_fuel(1000u, f, _args.d_a1));
            }},
        t->v());
  }

  /// Helper: flatten a list of rose trees to a flat list of nats.
  static std::shared_ptr<List<unsigned int>> flatten_rose_list_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<rose>>> &cs);
  /// rose_flatten t flattens a rose tree to a list (pre-order).
  static std::shared_ptr<List<unsigned int>>
  rose_flatten(const std::shared_ptr<rose> &t);
  /// Helper: compute maximum depth among a list of rose trees.
  __attribute__((pure)) static unsigned int
  depth_rose_list_fuel(const unsigned int fuel,
                       const std::shared_ptr<List<std::shared_ptr<rose>>> &cs);
  /// rose_depth t computes the depth of a rose tree.
  __attribute__((pure)) static unsigned int
  rose_depth(const std::shared_ptr<rose> &t);
  /// tree_max t1 t2 element-wise maximum of two trees.
  static std::shared_ptr<tree<unsigned int>>
  tree_max(std::shared_ptr<tree<unsigned int>> t1,
           std::shared_ptr<tree<unsigned int>> t2);
  /// Helper: extract values from trees.
  static std::shared_ptr<List<unsigned int>> extract_tree_values(
      const std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>> &ts);
  /// Helper: extract children from trees.
  static std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>>
  extract_tree_children(
      const std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>> &ts);
  /// tree_levels t returns list of lists, one per level (breadth-first).
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tree_levels_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>> &trees);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tree_levels(std::shared_ptr<tree<unsigned int>> t);
  /// count_nodes t returns tuple (node_count, sum_of_values).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  count_nodes(const std::shared_ptr<tree<unsigned int>> &t);

  /// mirror_equal t1 t2 checks if t1 and t2 are mirror images.
  template <typename T1>
  __attribute__((pure)) static bool
  mirror_equal(const std::shared_ptr<tree<T1>> &t1,
               const std::shared_ptr<tree<T1>> &t2) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t2;
      const std::shared_ptr<tree<T1>> t1;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s1;
      decltype(true) _s2;
    };

    struct _Call2 {
      bool _s0;
      decltype(true) _s1;
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
                const std::shared_ptr<tree<T1>> t2 = _f.t2;
                const std::shared_ptr<tree<T1>> t1 = _f.t1;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = std::visit(
                              Overloaded{
                                  [](const typename tree<T1>::Leaf _args0)
                                      -> bool { return true; },
                                  [](const typename tree<T1>::Node _args0)
                                      -> bool { return false; }},
                              t2->v());
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename tree<T1>::Leaf _args0)
                                      -> void { _result = false; },
                                  [&](const typename tree<T1>::Node _args0)
                                      -> void {
                                    _stack.push_back(
                                        _Call1{_args0.d_a2, _args.d_a0, true});
                                    _stack.push_back(
                                        _Enter{_args0.d_a0, _args.d_a2});
                                  }},
                              t2->v());
                        }},
                    t1->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s2});
                _stack.push_back(_Enter{_f._s0, _f._s1});
              },
              [&](_Call2 _f) { _result = ((_result && _f._s0) && _f._s1); }},
          _frame);
    }
    return _result;
  }

  /// tree_map f t applies f to all values in tree.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<tree<T2>>
  tree_map(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
      T2 _s1;
    };

    struct _Call2 {
      std::shared_ptr<tree<T2>> _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<tree<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> void {
                          _result = tree<T2>::ctor::Leaf_();
                        },
                        [&](const typename tree<T1>::Node _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0, f(_args.d_a1)});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = tree<T2>::ctor::Node_(_result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// Helper: append two lists of lists.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  append_list_lists(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &l1,
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> l2);
  /// Helper: prepend value to all lists in a list of lists.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  map_cons_to_all(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts);
  /// paths t returns all root-to-leaf paths in tree.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  paths(const std::shared_ptr<tree<unsigned int>> &t);
  /// collect_sorted t collects and sorts all tree values.
  static std::shared_ptr<List<unsigned int>>
  collect_unsorted(const std::shared_ptr<tree<unsigned int>> &t);
  /// Simple insertion sort for collect_sorted.
  static std::shared_ptr<List<unsigned int>>
  insert_sorted(const unsigned int x,
                const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  sort_list(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>> collect_sorted(
      const std::shared_ptr<tree<unsigned int>>
          &t); /// or_search p t searches tree for element satisfying predicate.

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  or_search(F0 &&p, const std::shared_ptr<tree<unsigned int>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<unsigned int>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<unsigned int>::Node &>()
                   .d_a0) _s0;
    };

    struct _Call2 {
      bool _s0;
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
                const std::shared_ptr<tree<unsigned int>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<unsigned int>::Leaf _args)
                            -> void { _result = false; },
                        [&](const typename tree<unsigned int>::Node _args)
                            -> void {
                          if (p(_args.d_a1)) {
                            _result = true;
                          } else {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2});
                          }
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = (_result || _f._s0); }},
          _frame);
    }
    return _result;
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> d_a0;
      std::shared_ptr<quadtree> d_a1;
      std::shared_ptr<quadtree> d_a2;
      std::shared_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<quadtree> QLeaf_(unsigned int a0) {
        return std::shared_ptr<quadtree>(new quadtree(QLeaf{a0}));
      }

      static std::shared_ptr<quadtree>
      Quad_(const std::shared_ptr<quadtree> &a0,
            const std::shared_ptr<quadtree> &a1,
            const std::shared_ptr<quadtree> &a2,
            const std::shared_ptr<quadtree> &a3) {
        return std::shared_ptr<quadtree>(new quadtree(Quad{a0, a1, a2, a3}));
      }

      static std::unique_ptr<quadtree> QLeaf_uptr(unsigned int a0) {
        return std::unique_ptr<quadtree>(new quadtree(QLeaf{a0}));
      }

      static std::unique_ptr<quadtree>
      Quad_uptr(const std::shared_ptr<quadtree> &a0,
                const std::shared_ptr<quadtree> &a1,
                const std::shared_ptr<quadtree> &a2,
                const std::shared_ptr<quadtree> &a3) {
        return std::unique_ptr<quadtree>(new quadtree(Quad{a0, a1, a2, a3}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1,
             std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1>
          F1>
  static T1 quadtree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<quadtree> &q) {
    struct _Enter {
      const std::shared_ptr<quadtree> q;
    };

    struct _Call1 {
      const std::shared_ptr<quadtree> _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      const std::shared_ptr<quadtree> _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{q});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<quadtree> q = _f.q;
                std::visit(
                    Overloaded{
                        [&](const typename quadtree::QLeaf _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename quadtree::Quad _args) -> void {
                          _stack.push_back(_Call1{
                              _args.d_a2, _args.d_a1, _args.d_a0, _args.d_a3,
                              _args.d_a2, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a3});
                        }},
                    q->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4,
                                        _f._s5, _f._s6});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4,
                                        _f._s5, _f._s6});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4,
                                        _f._s5, _f._s6});
                _stack.push_back(_Enter{_f._s2});
              },
              [&](_Call4 _f) {
                _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1,
                             _f._s3, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1,
             std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1>
          F1>
  static T1 quadtree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<quadtree> &q) {
    struct _Enter {
      const std::shared_ptr<quadtree> q;
    };

    struct _Call1 {
      const std::shared_ptr<quadtree> _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      const std::shared_ptr<quadtree> _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{q});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<quadtree> q = _f.q;
                std::visit(
                    Overloaded{
                        [&](const typename quadtree::QLeaf _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename quadtree::Quad _args) -> void {
                          _stack.push_back(_Call1{
                              _args.d_a2, _args.d_a1, _args.d_a0, _args.d_a3,
                              _args.d_a2, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a3});
                        }},
                    q->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4,
                                        _f._s5, _f._s6});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4,
                                        _f._s5, _f._s6});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4,
                                        _f._s5, _f._s6});
                _stack.push_back(_Enter{_f._s2});
              },
              [&](_Call4 _f) {
                _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1,
                             _f._s3, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// quad_sum t sums all values in a quadtree.
  __attribute__((pure)) static unsigned int
  quad_sum(const std::shared_ptr<quadtree> &t);
  /// Helper: max of 4 values using nested max.
  __attribute__((pure)) static unsigned int max4_impl(const unsigned int a,
                                                      const unsigned int b,
                                                      const unsigned int c,
                                                      const unsigned int d);
  /// quad_depth t computes depth of quadtree.
  __attribute__((pure)) static unsigned int
  quad_depth(const std::shared_ptr<quadtree> &t);

  /// Simple binary tree with values only at leaves.
  struct simple_tree {
    // TYPES
    struct SLeaf {
      unsigned int d_a0;
    };

    struct SNode {
      std::shared_ptr<simple_tree> d_a0;
      std::shared_ptr<simple_tree> d_a1;
    };

    using variant_t = std::variant<SLeaf, SNode>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit simple_tree(SLeaf _v) : d_v_(std::move(_v)) {}

    explicit simple_tree(SNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<simple_tree> SLeaf_(unsigned int a0) {
        return std::shared_ptr<simple_tree>(new simple_tree(SLeaf{a0}));
      }

      static std::shared_ptr<simple_tree>
      SNode_(const std::shared_ptr<simple_tree> &a0,
             const std::shared_ptr<simple_tree> &a1) {
        return std::shared_ptr<simple_tree>(new simple_tree(SNode{a0, a1}));
      }

      static std::unique_ptr<simple_tree> SLeaf_uptr(unsigned int a0) {
        return std::unique_ptr<simple_tree>(new simple_tree(SLeaf{a0}));
      }

      static std::unique_ptr<simple_tree>
      SNode_uptr(const std::shared_ptr<simple_tree> &a0,
                 const std::shared_ptr<simple_tree> &a1) {
        return std::unique_ptr<simple_tree>(new simple_tree(SNode{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<simple_tree>, T1,
                   std::shared_ptr<simple_tree>, T1>
                F1>
  static T1 simple_tree_rect(F0 &&f, F1 &&f0,
                             const std::shared_ptr<simple_tree> &s) {
    struct _Enter {
      const std::shared_ptr<simple_tree> s;
    };

    struct _Call1 {
      decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s0;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{s});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<simple_tree> s = _f.s;
                std::visit(
                    Overloaded{
                        [&](const typename simple_tree::SLeaf _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename simple_tree::SNode _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    s->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<simple_tree>, T1,
                   std::shared_ptr<simple_tree>, T1>
                F1>
  static T1 simple_tree_rec(F0 &&f, F1 &&f0,
                            const std::shared_ptr<simple_tree> &s) {
    struct _Enter {
      const std::shared_ptr<simple_tree> s;
    };

    struct _Call1 {
      decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s0;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
      decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{s});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<simple_tree> s = _f.s;
                std::visit(
                    Overloaded{
                        [&](const typename simple_tree::SLeaf _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename simple_tree::SNode _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    s->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// simple_tree_sum t sums all leaf values.
  __attribute__((pure)) static unsigned int
  simple_tree_sum(const std::shared_ptr<simple_tree> &t);
  /// count_paths_simple t n counts paths with sum n (simpler variant).
  __attribute__((pure)) static unsigned int
  count_paths_simple(const std::shared_ptr<simple_tree> &t,
                     const unsigned int n);
  /// Helper: compute minimum of three values.
  __attribute__((pure)) static unsigned int
  min3(const unsigned int a, const unsigned int b, const unsigned int c);
  /// Helper: compute maximum of three values.
  __attribute__((pure)) static unsigned int
  max3(const unsigned int a, const unsigned int b, const unsigned int c);
  /// tree_min_max t finds minimum and maximum values in tree.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  tree_min_max(const std::shared_ptr<tree<unsigned int>> &t);
  /// all_paths_sum t sums all root-to-leaf path sums.
  __attribute__((pure)) static unsigned int
  all_paths_sum(const std::shared_ptr<tree<unsigned int>> &t);
  /// tree_contains x t checks if value exists in tree.
  __attribute__((pure)) static bool
  tree_contains(const unsigned int x,
                const std::shared_ptr<tree<unsigned int>> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
