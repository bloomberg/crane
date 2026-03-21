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

struct LoopifyTrees {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<list<T1>> l = _f.l;
                       std::visit(
                           Overloaded{
                               [&](const typename list<T1>::Nil _args) -> T2 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename list<T1>::Cons _args) -> T2 {
                                 _stack.push_back(
                                     _Call1{_args.d_a1, _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                                 return {};
                               }},
                           l->v());
                     },
                     [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<list<T1>> l = _f.l;
                       std::visit(
                           Overloaded{
                               [&](const typename list<T1>::Nil _args) -> T2 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename list<T1>::Cons _args) -> T2 {
                                 _stack.push_back(
                                     _Call1{_args.d_a1, _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                                 return {};
                               }},
                           l->v());
                     },
                     [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

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
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
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
                std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename tree<T1>::Node _args) -> T2 {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                                 return {};
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
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
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
                std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree<T1>::Leaf _args) -> T2 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename tree<T1>::Node _args) -> T2 {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                                 return {};
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
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      typename tree<T1>::Node _s0;
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
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<tree<T1>> t = _f.t;
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf _args)
                                          -> unsigned int {
                                        _result = 0u;
                                        return {};
                                      },
                                      [&](const typename tree<T1>::Node _args)
                                          -> unsigned int {
                                        _stack.push_back(_Call1{_args});
                                        _stack.push_back(_Enter{_args.d_a0});
                                        return {};
                                      }},
                           t->v());
                     },
                     [&](_Call1 _f) {
                       typename tree<T1>::Node _args = _f._s0;
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
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
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
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<tree<T1>> t = _f.t;
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf _args)
                                          -> unsigned int {
                                        _result = 0u;
                                        return {};
                                      },
                                      [&](const typename tree<T1>::Node _args)
                                          -> unsigned int {
                                        _stack.push_back(_Call1{_args.d_a0});
                                        _stack.push_back(_Enter{_args.d_a2});
                                        return {};
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
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s1;
    };

    struct _Call2 {
      std::shared_ptr<tree<T1>> _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<tree<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<tree<T1>> t = _f.t;
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf _args)
                                          -> std::shared_ptr<tree<T1>> {
                                        _result = tree<T1>::ctor::Leaf_();
                                        return {};
                                      },
                                      [&](const typename tree<T1>::Node _args)
                                          -> std::shared_ptr<tree<T1>> {
                                        _stack.push_back(
                                            _Call1{_args.d_a2, _args.d_a1});
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
                       _result = tree<T1>::ctor::Node_(_result, _f._s1, _f._s0);
                     }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static bool
  same_shape(const std::shared_ptr<tree<T1>> &t1,
             const std::shared_ptr<tree<T2>> &t2) {
    struct _Enter {
      std::shared_ptr<tree<T2>> t2;
      std::shared_ptr<tree<T1>> t1;
    };

    struct _Call1 {
      typename tree<T2>::Node _s0;
      typename tree<T1>::Node _s1;
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
                std::shared_ptr<tree<T2>> t2 = _f.t2;
                std::shared_ptr<tree<T1>> t1 = _f.t1;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> bool {
                          _result = std::visit(
                              Overloaded{
                                  [](const typename tree<T2>::Leaf _args0)
                                      -> bool { return true; },
                                  [](const typename tree<T2>::Node _args0)
                                      -> bool { return false; }},
                              t2->v());
                          return {};
                        },
                        [&](const typename tree<T1>::Node _args) -> bool {
                          std::visit(
                              Overloaded{
                                  [&](const typename tree<T2>::Leaf _args0)
                                      -> bool {
                                    _result = false;
                                    return {};
                                  },
                                  [&](const typename tree<T2>::Node _args0)
                                      -> bool {
                                    _stack.push_back(_Call1{_args0, _args});
                                    _stack.push_back(
                                        _Enter{_args0.d_a0, _args.d_a0});
                                    return {};
                                  }},
                              t2->v());
                          return {};
                        }},
                    t1->v());
              },
              [&](_Call1 _f) {
                typename tree<T2>::Node _args0 = _f._s0;
                typename tree<T1>::Node _args = _f._s1;
                if (_result) {
                  _stack.push_back(_Enter{_args0.d_a2, _args.d_a2});
                } else {
                  _result = false;
                }
              }},
          _frame);
    }
    return _result;
  }

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
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  count_leaves(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
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
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<tree<T1>> t = _f.t;
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf _args)
                                          -> unsigned int {
                                        _result = 1u;
                                        return {};
                                      },
                                      [&](const typename tree<T1>::Node _args)
                                          -> unsigned int {
                                        _stack.push_back(_Call1{_args.d_a0});
                                        _stack.push_back(_Enter{_args.d_a2});
                                        return {};
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

  __attribute__((pure)) static unsigned int
  leaf_sum(const std::shared_ptr<tree<unsigned int>> &t);
  static std::shared_ptr<tree<unsigned int>>
  insert_bst(const unsigned int x,
             const std::shared_ptr<tree<unsigned int>> &t);

  template <typename T1>
  static std::shared_ptr<list<T1>>
  tree_to_list(const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s1;
    };

    struct _Call2 {
      std::shared_ptr<list<T1>> _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                std::shared_ptr<tree<T1>> t = _f.t;
                std::function<std::shared_ptr<list<T1>>(
                    std::shared_ptr<list<T1>>, std::shared_ptr<list<T1>>)>
                    app;
                app = [&](std::shared_ptr<list<T1>> l1,
                          std::shared_ptr<list<T1>> l2)
                    -> std::shared_ptr<list<T1>> {
                  struct _Enter {
                    std::shared_ptr<list<T1>> l2;
                    std::shared_ptr<list<T1>> l1;
                  };
                  struct _Call1 {
                    decltype(std::declval<typename list<T1>::Cons &>()
                                 .d_a0) _s0;
                  };
                  using _Frame = std::variant<_Enter, _Call1>;
                  std::shared_ptr<list<T1>> _result{};
                  std::vector<_Frame> _stack;
                  _stack.push_back(_Enter{l2, l1});
                  while (!_stack.empty()) {
                    _Frame _frame = std::move(_stack.back());
                    _stack.pop_back();
                    std::visit(
                        Overloaded{
                            [&](_Enter _f) {
                              std::shared_ptr<list<T1>> l2 = _f.l2;
                              std::shared_ptr<list<T1>> l1 = _f.l1;
                              std::visit(
                                  Overloaded{
                                      [&](const typename list<T1>::Nil _args)
                                          -> std::shared_ptr<list<T1>> {
                                        _result = std::move(l2);
                                        return {};
                                      },
                                      [&](const typename list<T1>::Cons _args)
                                          -> std::shared_ptr<list<T1>> {
                                        _stack.push_back(_Call1{_args.d_a0});
                                        _stack.push_back(
                                            _Enter{std::move(l2), _args.d_a1});
                                        return {};
                                      }},
                                  l1->v());
                            },
                            [&](_Call1 _f) {
                              _result = list<T1>::ctor::Cons_(_f._s0, _result);
                            }},
                        _frame);
                  }
                  return _result;
                };
                std::visit(Overloaded{[&](const typename tree<T1>::Leaf _args0)
                                          -> std::shared_ptr<list<T1>> {
                                        _result = list<T1>::ctor::Nil_();
                                        return {};
                                      },
                                      [&](const typename tree<T1>::Node _args0)
                                          -> std::shared_ptr<list<T1>> {
                                        _stack.push_back(
                                            _Call1{_args0.d_a0, _args0.d_a1});
                                        _stack.push_back(_Enter{_args0.d_a2});
                                        return {};
                                      }},
                           t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = app(_result, list<T1>::ctor::Cons_(_f._s1, _f._s0));
              }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  count_paths(const std::shared_ptr<tree<unsigned int>> &t,
              const unsigned int n);
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
      std::shared_ptr<ternary> t;
    };

    struct _Call1 {
      std::shared_ptr<ternary> _s0;
      std::shared_ptr<ternary> _s1;
      decltype(std::declval<typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call2 {
      T1 _s0;
      std::shared_ptr<ternary> _s1;
      decltype(std::declval<typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<typename ternary::TNode &>().d_a0) _s5;
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
                std::shared_ptr<ternary> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename ternary::TLeaf _args) -> T1 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename ternary::TNode _args) -> T1 {
                                 _stack.push_back(_Call1{
                                     _args.d_a1, _args.d_a0, _args.d_a3,
                                     _args.d_a2, _args.d_a1, _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                                 return {};
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
      std::shared_ptr<ternary> t;
    };

    struct _Call1 {
      std::shared_ptr<ternary> _s0;
      std::shared_ptr<ternary> _s1;
      decltype(std::declval<typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call2 {
      T1 _s0;
      std::shared_ptr<ternary> _s1;
      decltype(std::declval<typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<typename ternary::TNode &>().d_a0) _s5;
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
                std::shared_ptr<ternary> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename ternary::TLeaf _args) -> T1 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename ternary::TNode _args) -> T1 {
                                 _stack.push_back(_Call1{
                                     _args.d_a1, _args.d_a0, _args.d_a3,
                                     _args.d_a2, _args.d_a1, _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                                 return {};
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
  ternary_depth(const std::shared_ptr<ternary> &t);

  struct rose {
    // TYPES
    struct RNode {
      unsigned int d_a0;
      std::shared_ptr<list<std::shared_ptr<rose>>> d_a1;
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
             const std::shared_ptr<list<std::shared_ptr<rose>>> &a1) {
        return std::shared_ptr<rose>(new rose(RNode{a0, a1}));
      }

      static std::unique_ptr<rose>
      RNode_uptr(unsigned int a0,
                 const std::shared_ptr<list<std::shared_ptr<rose>>> &a1) {
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
      MapsTo<T1, unsigned int, std::shared_ptr<list<std::shared_ptr<rose>>>> F0>
  static T1 rose_rect(F0 &&f, const std::shared_ptr<rose> &r) {
    return std::visit(Overloaded{[&](const typename rose::RNode _args) -> T1 {
                        return f(_args.d_a0, _args.d_a1);
                      }},
                      r->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, std::shared_ptr<list<std::shared_ptr<rose>>>> F0>
  static T1 rose_rec(F0 &&f, const std::shared_ptr<rose> &r) {
    return std::visit(Overloaded{[&](const typename rose::RNode _args) -> T1 {
                        return f(_args.d_a0, _args.d_a1);
                      }},
                      r->v());
  }

  __attribute__((pure)) static unsigned int
  rose_sum(const std::shared_ptr<rose> &t);

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<rose> rose_map(F0 &&f,
                                        const std::shared_ptr<rose> &t) {
    struct _Enter {
      std::shared_ptr<rose> t;
    };

    using _Frame = std::variant<_Enter>;
    std::shared_ptr<rose> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
            std::shared_ptr<rose> t = _f.t;
            std::visit(
                Overloaded{[&](const typename rose::RNode _args)
                               -> std::shared_ptr<rose> {
                  std::function<std::shared_ptr<list<std::shared_ptr<rose>>>(
                      std::shared_ptr<list<std::shared_ptr<rose>>>)>
                      map_children;
                  map_children =
                      [&](std::shared_ptr<list<std::shared_ptr<rose>>> cs)
                      -> std::shared_ptr<list<std::shared_ptr<rose>>> {
                    struct _Enter {
                      std::shared_ptr<list<std::shared_ptr<rose>>> cs;
                    };
                    struct _Call1 {
                      decltype(rose_map(
                          f, std::declval<
                                 typename list<std::shared_ptr<rose>>::Cons &>()
                                 .d_a0)) _s0;
                    };
                    using _Frame = std::variant<_Enter, _Call1>;
                    std::shared_ptr<list<std::shared_ptr<rose>>> _result{};
                    std::vector<_Frame> _stack;
                    _stack.push_back(_Enter{cs});
                    while (!_stack.empty()) {
                      _Frame _frame = std::move(_stack.back());
                      _stack.pop_back();
                      std::visit(
                          Overloaded{
                              [&](_Enter _f) {
                                std::shared_ptr<list<std::shared_ptr<rose>>>
                                    cs = _f.cs;
                                std::visit(
                                    Overloaded{
                                        [&](const typename list<
                                            std::shared_ptr<rose>>::Nil _args0)
                                            -> std::shared_ptr<
                                                list<std::shared_ptr<rose>>> {
                                          _result =
                                              list<std::shared_ptr<rose>>::
                                                  ctor::Nil_();
                                          return {};
                                        },
                                        [&](const typename list<
                                            std::shared_ptr<rose>>::Cons _args0)
                                            -> std::shared_ptr<
                                                list<std::shared_ptr<rose>>> {
                                          _stack.push_back(
                                              _Call1{rose_map(f, _args0.d_a0)});
                                          _stack.push_back(_Enter{_args0.d_a1});
                                          return {};
                                        }},
                                    cs->v());
                              },
                              [&](_Call1 _f) {
                                _result =
                                    list<std::shared_ptr<rose>>::ctor::Cons_(
                                        _f._s0, _result);
                              }},
                          _frame);
                    }
                    return _result;
                  };
                  _result = rose::ctor::RNode_(f(_args.d_a0),
                                               map_children(_args.d_a1));
                  return {};
                }},
                t->v());
          }},
          _frame);
    }
    return _result;
  }

  static std::shared_ptr<list<unsigned int>>
  append_lists(const std::shared_ptr<list<unsigned int>> &l1,
               std::shared_ptr<list<unsigned int>> l2);
  static std::shared_ptr<list<unsigned int>>
  rose_flatten(const std::shared_ptr<rose> &t);
  __attribute__((pure)) static unsigned int
  rose_depth(const std::shared_ptr<rose> &t);
  static std::shared_ptr<tree<unsigned int>>
  tree_max(std::shared_ptr<tree<unsigned int>> t1,
           std::shared_ptr<tree<unsigned int>> t2);
  static std::shared_ptr<list<unsigned int>> extract_tree_values(
      const std::shared_ptr<list<std::shared_ptr<tree<unsigned int>>>> &ts);
  static std::shared_ptr<list<std::shared_ptr<tree<unsigned int>>>>
  extract_tree_children(
      const std::shared_ptr<list<std::shared_ptr<tree<unsigned int>>>> &ts);
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  tree_levels_fuel(
      const unsigned int fuel,
      const std::shared_ptr<list<std::shared_ptr<tree<unsigned int>>>> &trees);
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  tree_levels(std::shared_ptr<tree<unsigned int>> t);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  count_nodes(const std::shared_ptr<tree<unsigned int>> &t);

  template <typename T1>
  __attribute__((pure)) static bool
  mirror_equal(const std::shared_ptr<tree<T1>> &t1,
               const std::shared_ptr<tree<T1>> &t2) {
    struct _Enter {
      std::shared_ptr<tree<T1>> t2;
      std::shared_ptr<tree<T1>> t1;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s1;
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
                std::shared_ptr<tree<T1>> t2 = _f.t2;
                std::shared_ptr<tree<T1>> t1 = _f.t1;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf _args) -> bool {
                          _result = std::visit(
                              Overloaded{
                                  [](const typename tree<T1>::Leaf _args0)
                                      -> bool { return true; },
                                  [](const typename tree<T1>::Node _args0)
                                      -> bool { return false; }},
                              t2->v());
                          return {};
                        },
                        [&](const typename tree<T1>::Node _args) -> bool {
                          std::visit(
                              Overloaded{
                                  [&](const typename tree<T1>::Leaf _args0)
                                      -> bool {
                                    _result = false;
                                    return {};
                                  },
                                  [&](const typename tree<T1>::Node _args0)
                                      -> bool {
                                    _stack.push_back(
                                        _Call1{_args0.d_a2, _args.d_a0, true});
                                    _stack.push_back(
                                        _Enter{_args0.d_a0, _args.d_a2});
                                    return {};
                                  }},
                              t2->v());
                          return {};
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

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<tree<T2>>
  tree_map(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
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
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<tree<T1>> t = _f.t;
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf _args)
                                          -> std::shared_ptr<tree<T2>> {
                                        _result = tree<T2>::ctor::Leaf_();
                                        return {};
                                      },
                                      [&](const typename tree<T1>::Node _args)
                                          -> std::shared_ptr<tree<T2>> {
                                        _stack.push_back(
                                            _Call1{_args.d_a0, f(_args.d_a1)});
                                        _stack.push_back(_Enter{_args.d_a2});
                                        return {};
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

  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  append_list_lists(
      const std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>> &l1,
      std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>> l2);
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  map_cons_to_all(
      const unsigned int x,
      const std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>> &lsts);
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  paths(const std::shared_ptr<tree<unsigned int>> &t);
  static std::shared_ptr<list<unsigned int>>
  collect_unsorted(const std::shared_ptr<tree<unsigned int>> &t);
  static std::shared_ptr<list<unsigned int>>
  insert_sorted(const unsigned int x,
                const std::shared_ptr<list<unsigned int>> &l);
  static std::shared_ptr<list<unsigned int>>
  sort_list(const std::shared_ptr<list<unsigned int>> &l);
  static std::shared_ptr<list<unsigned int>>
  collect_sorted(const std::shared_ptr<tree<unsigned int>> &t);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  or_search(F0 &&p, const std::shared_ptr<tree<unsigned int>> &t) {
    struct _Enter {
      std::shared_ptr<tree<unsigned int>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<unsigned int>::Node &>().d_a0) _s0;
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
                std::shared_ptr<tree<unsigned int>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<unsigned int>::Leaf _args)
                            -> bool {
                          _result = false;
                          return {};
                        },
                        [&](const typename tree<unsigned int>::Node _args)
                            -> bool {
                          if (p(_args.d_a1)) {
                            _result = true;
                          } else {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2});
                          }
                          return {};
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
      std::shared_ptr<quadtree> q;
    };

    struct _Call1 {
      std::shared_ptr<quadtree> _s0;
      std::shared_ptr<quadtree> _s1;
      std::shared_ptr<quadtree> _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call2 {
      T1 _s0;
      std::shared_ptr<quadtree> _s1;
      std::shared_ptr<quadtree> _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      std::shared_ptr<quadtree> _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{q});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<quadtree> q = _f.q;
                       std::visit(
                           Overloaded{
                               [&](const typename quadtree::QLeaf _args) -> T1 {
                                 _result = f(_args.d_a0);
                                 return {};
                               },
                               [&](const typename quadtree::Quad _args) -> T1 {
                                 _stack.push_back(_Call1{_args.d_a2, _args.d_a1,
                                                         _args.d_a0, _args.d_a3,
                                                         _args.d_a2, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a3});
                                 return {};
                               }},
                           q->v());
                     },
                     [&](_Call1 _f) {
                       _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3,
                                               _f._s4, _f._s5, _f._s6});
                       _stack.push_back(_Enter{_f._s0});
                     },
                     [&](_Call2 _f) {
                       _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3,
                                               _f._s4, _f._s5, _f._s6});
                       _stack.push_back(_Enter{_f._s1});
                     },
                     [&](_Call3 _f) {
                       _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3,
                                               _f._s4, _f._s5, _f._s6});
                       _stack.push_back(_Enter{_f._s2});
                     },
                     [&](_Call4 _f) {
                       _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4,
                                    _f._s1, _f._s3, _f._s0);
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
      std::shared_ptr<quadtree> q;
    };

    struct _Call1 {
      std::shared_ptr<quadtree> _s0;
      std::shared_ptr<quadtree> _s1;
      std::shared_ptr<quadtree> _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call2 {
      T1 _s0;
      std::shared_ptr<quadtree> _s1;
      std::shared_ptr<quadtree> _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      std::shared_ptr<quadtree> _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      decltype(std::declval<typename quadtree::Quad &>().d_a3) _s3;
      decltype(std::declval<typename quadtree::Quad &>().d_a2) _s4;
      decltype(std::declval<typename quadtree::Quad &>().d_a1) _s5;
      decltype(std::declval<typename quadtree::Quad &>().d_a0) _s6;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{q});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       std::shared_ptr<quadtree> q = _f.q;
                       std::visit(
                           Overloaded{
                               [&](const typename quadtree::QLeaf _args) -> T1 {
                                 _result = f(_args.d_a0);
                                 return {};
                               },
                               [&](const typename quadtree::Quad _args) -> T1 {
                                 _stack.push_back(_Call1{_args.d_a2, _args.d_a1,
                                                         _args.d_a0, _args.d_a3,
                                                         _args.d_a2, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a3});
                                 return {};
                               }},
                           q->v());
                     },
                     [&](_Call1 _f) {
                       _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3,
                                               _f._s4, _f._s5, _f._s6});
                       _stack.push_back(_Enter{_f._s0});
                     },
                     [&](_Call2 _f) {
                       _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3,
                                               _f._s4, _f._s5, _f._s6});
                       _stack.push_back(_Enter{_f._s1});
                     },
                     [&](_Call3 _f) {
                       _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3,
                                               _f._s4, _f._s5, _f._s6});
                       _stack.push_back(_Enter{_f._s2});
                     },
                     [&](_Call4 _f) {
                       _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4,
                                    _f._s1, _f._s3, _f._s0);
                     }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  quad_sum(const std::shared_ptr<quadtree> &t);
  __attribute__((pure)) static unsigned int max4_impl(const unsigned int a,
                                                      const unsigned int b,
                                                      const unsigned int c,
                                                      const unsigned int d);
  __attribute__((pure)) static unsigned int
  quad_depth(const std::shared_ptr<quadtree> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
