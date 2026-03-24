#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

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
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    std::shared_ptr<List<t_A>> _loop_m = m;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil _args) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _loop_m;
                } else {
                  _head = _loop_m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::ctor::Cons_(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                List *_next_self = _loop_m.get();
                std::shared_ptr<List<t_A>> _next_m = _args.d_a1;
                _loop_self = std::move(_next_self);
                _loop_m = std::move(_next_m);
              }},
          _loop_self->v());
    }
    return _head;
  }
};

struct LoopifyTreePaths {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
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

      static std::shared_ptr<tree> Leaf_() {
        return std::shared_ptr<tree>(new tree(Leaf{}));
      }

      static std::shared_ptr<tree> Node_(const std::shared_ptr<tree> &a0,
                                         unsigned int a1,
                                         const std::shared_ptr<tree> &a2) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1, a2}));
      }

      static std::unique_ptr<tree> Leaf_uptr() {
        return std::unique_ptr<tree>(new tree(Leaf{}));
      }

      static std::unique_ptr<tree> Node_uptr(const std::shared_ptr<tree> &a0,
                                             unsigned int a1,
                                             const std::shared_ptr<tree> &a2) {
        return std::unique_ptr<tree>(new tree(Node{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree::Leaf _args) -> void {
                                 _result = f;
                               },
                               [&](const typename tree::Node _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
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

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree::Leaf _args) -> void {
                                 _result = f;
                               },
                               [&](const typename tree::Node _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
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

  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> map_cons(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  paths(const std::shared_ptr<tree> &t);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      unsigned int d_a0;
    };

    struct BNode {
      std::shared_ptr<bool_tree> d_a0;
      std::shared_ptr<bool_tree> d_a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit bool_tree(BLeaf _v) : d_v_(std::move(_v)) {}

    explicit bool_tree(BNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<bool_tree> BLeaf_(unsigned int a0) {
        return std::shared_ptr<bool_tree>(new bool_tree(BLeaf{a0}));
      }

      static std::shared_ptr<bool_tree>
      BNode_(const std::shared_ptr<bool_tree> &a0,
             const std::shared_ptr<bool_tree> &a1) {
        return std::shared_ptr<bool_tree>(new bool_tree(BNode{a0, a1}));
      }

      static std::unique_ptr<bool_tree> BLeaf_uptr(unsigned int a0) {
        return std::unique_ptr<bool_tree>(new bool_tree(BLeaf{a0}));
      }

      static std::unique_ptr<bool_tree>
      BNode_uptr(const std::shared_ptr<bool_tree> &a0,
                 const std::shared_ptr<bool_tree> &a1) {
        return std::unique_ptr<bool_tree>(new bool_tree(BNode{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<bool_tree>, T1, std::shared_ptr<bool_tree>, T1>
          F1>
  static T1 bool_tree_rect(F0 &&f, F1 &&f0,
                           const std::shared_ptr<bool_tree> &b) {
    struct _Enter {
      const std::shared_ptr<bool_tree> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s0;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<bool_tree> b = _f.b;
                std::visit(
                    Overloaded{
                        [&](const typename bool_tree::BLeaf _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename bool_tree::BNode _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    b->v());
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

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<bool_tree>, T1, std::shared_ptr<bool_tree>, T1>
          F1>
  static T1 bool_tree_rec(F0 &&f, F1 &&f0,
                          const std::shared_ptr<bool_tree> &b) {
    struct _Enter {
      const std::shared_ptr<bool_tree> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s0;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<bool_tree> b = _f.b;
                std::visit(
                    Overloaded{
                        [&](const typename bool_tree::BLeaf _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename bool_tree::BNode _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    b->v());
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

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  or_search(F0 &&p, const std::shared_ptr<bool_tree> &t) {
    struct _Enter {
      const std::shared_ptr<bool_tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s0;
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
                const std::shared_ptr<bool_tree> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename bool_tree::BLeaf _args) -> void {
                          _result = p(_args.d_a0);
                        },
                        [&](const typename bool_tree::BNode _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
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

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  and_search(F0 &&p, const std::shared_ptr<bool_tree> &t) {
    struct _Enter {
      const std::shared_ptr<bool_tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s0;
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
                const std::shared_ptr<bool_tree> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename bool_tree::BLeaf _args) -> void {
                          _result = p(_args.d_a0);
                        },
                        [&](const typename bool_tree::BNode _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = (_result && _f._s0); }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  count_paths_sum_aux(const unsigned int acc, const unsigned int target,
                      const std::shared_ptr<tree> &t);
  __attribute__((pure)) static unsigned int
  count_paths_sum(const unsigned int target, const std::shared_ptr<tree> &t);
  __attribute__((
      pure)) static std::optional<std::shared_ptr<List<unsigned int>>>
  find_path_sum(const unsigned int acc, const unsigned int target,
                const std::shared_ptr<tree> &t);
  __attribute__((pure)) static unsigned int
  max_path_sum(const std::shared_ptr<tree> &t);

  static std::shared_ptr<List<unsigned int>>
  flatten_paths(const std::shared_ptr<tree> &t);
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
