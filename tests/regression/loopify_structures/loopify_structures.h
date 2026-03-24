#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

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

/// Nested and complex data structures.
struct LoopifyStructures {
  /// Nested list: elements or nested lists.
  struct nested {
    // TYPES
    struct Elem {
      unsigned int d_a0;
    };

    struct NList {
      std::shared_ptr<List<std::shared_ptr<nested>>> d_a0;
    };

    using variant_t = std::variant<Elem, NList>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit nested(Elem _v) : d_v_(std::move(_v)) {}

    explicit nested(NList _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<nested> Elem_(unsigned int a0) {
        return std::shared_ptr<nested>(new nested(Elem{a0}));
      }

      static std::shared_ptr<nested>
      NList_(const std::shared_ptr<List<std::shared_ptr<nested>>> &a0) {
        return std::shared_ptr<nested>(new nested(NList{a0}));
      }

      static std::unique_ptr<nested> Elem_uptr(unsigned int a0) {
        return std::unique_ptr<nested>(new nested(Elem{a0}));
      }

      static std::unique_ptr<nested>
      NList_uptr(const std::shared_ptr<List<std::shared_ptr<nested>>> &a0) {
        return std::unique_ptr<nested>(new nested(NList{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<List<std::shared_ptr<nested>>>> F1>
  static T1 nested_rect(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(Overloaded{[&](const typename nested::Elem _args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename nested::NList _args) -> T1 {
                                   return f0(_args.d_a0);
                                 }},
                      n->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<List<std::shared_ptr<nested>>>> F1>
  static T1 nested_rec(F0 &&f, F1 &&f0, const std::shared_ptr<nested> &n) {
    return std::visit(Overloaded{[&](const typename nested::Elem _args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename nested::NList _args) -> T1 {
                                   return f0(_args.d_a0);
                                 }},
                      n->v());
  }

  /// Helper: sum all elements in a list of nested structures.
  /// Handles both tree and list levels in one function for full loopification.
  __attribute__((pure)) static unsigned int
  sum_nested_list_fuel(const unsigned int fuel,
                       const std::shared_ptr<List<std::shared_ptr<nested>>> &l);
  /// nested_sum n sums all elements in a nested structure.
  __attribute__((pure)) static unsigned int
  nested_sum(const std::shared_ptr<nested> &n);
  /// Helper: compute max depth among a list of nested structures.
  __attribute__((pure)) static unsigned int depth_nested_list_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<nested>>> &l);
  /// nested_depth n computes maximum nesting depth.
  __attribute__((pure)) static unsigned int
  nested_depth(const std::shared_ptr<nested> &n);
  /// Helper: flatten a list of nested structures to a flat list of nats.
  static std::shared_ptr<List<unsigned int>> flatten_nested_list_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<nested>>> &l);
  /// nested_flatten n flattens to a regular list.
  static std::shared_ptr<List<unsigned int>>
  nested_flatten(const std::shared_ptr<nested> &n);

  /// Quadtree: leaf or 4-way branch.
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

  /// quad_sum t sums all values in quadtree.
  __attribute__((pure)) static unsigned int
  quad_sum(const std::shared_ptr<quadtree> &t);
  /// quad_depth t computes quadtree depth.
  __attribute__((pure)) static unsigned int
  quad_depth(const std::shared_ptr<quadtree> &t);

  /// quad_map f t applies function to all leaves.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<quadtree>
  quad_map(F0 &&f, const std::shared_ptr<quadtree> &t) {
    struct _Enter {
      const std::shared_ptr<quadtree> t;
    };

    struct _Call1 {
      const std::shared_ptr<quadtree> _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
    };

    struct _Call2 {
      std::shared_ptr<quadtree> _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
    };

    struct _Call3 {
      std::shared_ptr<quadtree> _s0;
      std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
    };

    struct _Call4 {
      std::shared_ptr<quadtree> _s0;
      std::shared_ptr<quadtree> _s1;
      std::shared_ptr<quadtree> _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    std::shared_ptr<quadtree> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<quadtree> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename quadtree::QLeaf _args) -> void {
                          _result = quadtree::ctor::QLeaf_(f(_args.d_a0));
                        },
                        [&](const typename quadtree::Quad _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a2, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a3});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_f._s0, _result, _f._s2});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_f._s0, _f._s1, _result});
                _stack.push_back(_Enter{_f._s2});
              },
              [&](_Call4 _f) {
                _result =
                    quadtree::ctor::Quad_(_result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// find_opt p l finds first element satisfying predicate, returns option.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_opt(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::optional<unsigned int> _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = std::optional<unsigned int>();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _result = std::make_optional<unsigned int>(
                                    _args.d_a0);
                                _continue = false;
                              } else {
                                _loop_l = _args.d_a1;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <MapsTo<std::optional<unsigned int>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  map_opt(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
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
                      .d_a1 = List<unsigned int>::ctor::Nil_();
                } else {
                  _head = List<unsigned int>::ctor::Nil_();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (f(_args.d_a0).has_value()) {
                  unsigned int y = *f(_args.d_a0);
                  auto _cell = List<unsigned int>::ctor::Cons_(y, nullptr);
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

  /// filter_map p f l filters and maps in one pass.
  template <MapsTo<bool, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  filter_map(F0 &&p, F1 &&f, const std::shared_ptr<List<unsigned int>> &l) {
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
                      .d_a1 = List<unsigned int>::ctor::Nil_();
                } else {
                  _head = List<unsigned int>::ctor::Nil_();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (p(_args.d_a0)) {
                  auto _cell =
                      List<unsigned int>::ctor::Cons_(f(_args.d_a0), nullptr);
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

  /// find_first_some l finds first Some value in list of options.
  __attribute__((pure)) static std::optional<unsigned int>
  find_first_some(const std::shared_ptr<List<std::optional<unsigned int>>> &l);

  /// Tree type with values in leaves.
  struct ltree {
    // TYPES
    struct LLeaf {
      unsigned int d_a0;
    };

    struct LNode {
      unsigned int d_a0;
      std::shared_ptr<ltree> d_a1;
      std::shared_ptr<ltree> d_a2;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit ltree(LLeaf _v) : d_v_(std::move(_v)) {}

    explicit ltree(LNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<ltree> LLeaf_(unsigned int a0) {
        return std::shared_ptr<ltree>(new ltree(LLeaf{a0}));
      }

      static std::shared_ptr<ltree> LNode_(unsigned int a0,
                                           const std::shared_ptr<ltree> &a1,
                                           const std::shared_ptr<ltree> &a2) {
        return std::shared_ptr<ltree>(new ltree(LNode{a0, a1, a2}));
      }

      static std::unique_ptr<ltree> LLeaf_uptr(unsigned int a0) {
        return std::unique_ptr<ltree>(new ltree(LLeaf{a0}));
      }

      static std::unique_ptr<ltree>
      LNode_uptr(unsigned int a0, const std::shared_ptr<ltree> &a1,
                 const std::shared_ptr<ltree> &a2) {
        return std::unique_ptr<ltree>(new ltree(LNode{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<ltree>, T1,
                   std::shared_ptr<ltree>, T1>
                F1>
  static T1 ltree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<ltree> &l) {
    struct _Enter {
      const std::shared_ptr<ltree> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename ltree::LNode &>().d_a1) _s0;
      decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
      decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
      decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
      decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
      decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<ltree> l = _f.l;
                std::visit(
                    Overloaded{[&](const typename ltree::LLeaf _args) -> void {
                                 _result = f(_args.d_a0);
                               },
                               [&](const typename ltree::LNode _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a1, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    l->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<ltree>, T1,
                   std::shared_ptr<ltree>, T1>
                F1>
  static T1 ltree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<ltree> &l) {
    struct _Enter {
      const std::shared_ptr<ltree> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename ltree::LNode &>().d_a1) _s0;
      decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
      decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
      decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
      decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
      decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<ltree> l = _f.l;
                std::visit(
                    Overloaded{[&](const typename ltree::LLeaf _args) -> void {
                                 _result = f(_args.d_a0);
                               },
                               [&](const typename ltree::LNode _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a1, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    l->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// ltree_max t1 t2 element-wise max of two leaf-trees.
  static std::shared_ptr<ltree> ltree_max(std::shared_ptr<ltree> t1,
                                          std::shared_ptr<ltree> t2);
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
