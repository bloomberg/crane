#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

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

struct LoopifyPolymorphic {
  template <typename T1>
  __attribute__((pure)) static unsigned int
  poly_length(const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
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
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
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

  template <typename T1>
  static std::shared_ptr<List<T1>>
  poly_reverse(const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      decltype(List<T1>::ctor::Cons_(
          std::declval<const typename List<T1>::Cons &>().d_a0,
          List<T1>::ctor::Nil_())) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = List<T1>::ctor::Nil_();
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{List<T1>::ctor::Cons_(
                              _args.d_a0, List<T1>::ctor::Nil_())});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = _result->app(_f._s0); }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  poly_append(const std::shared_ptr<List<T1>> &l1,
              std::shared_ptr<List<T1>> l2) {
    struct _Enter {
      std::shared_ptr<List<T1>> l2;
      const std::shared_ptr<List<T1>> l1;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<T1>::Cons &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l2, l1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                std::shared_ptr<List<T1>> l2 = _f.l2;
                const std::shared_ptr<List<T1>> l1 = _f.l1;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = std::move(l2);
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        }},
                    l1->v());
              },
              [&](_Call1 _f) {
                _result = List<T1>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static std::optional<T1>
  poly_last(const std::shared_ptr<List<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{[&](const typename List<T1>::Nil _args) {
                       _result = std::nullopt;
                       _continue = false;
                     },
                     [&](const typename List<T1>::Cons _args) {
                       std::visit(
                           Overloaded{
                               [&](const typename List<T1>::Nil _args0) {
                                 _result = std::make_optional<T1>(_args.d_a0);
                                 _continue = false;
                               },
                               [&](const typename List<T1>::Cons _args0) {
                                 _loop_l = _args.d_a1;
                               }},
                           _args.d_a1->v());
                     }},
          _loop_l->v());
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  poly_take(const unsigned int n, const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
      const unsigned int n;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<T1>::Cons &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                const unsigned int n = _f.n;
                if (n <= 0) {
                  _result = List<T1>::ctor::Nil_();
                } else {
                  unsigned int n_ = n - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename List<T1>::Nil _args) -> void {
                            _result = List<T1>::ctor::Nil_();
                          },
                          [&](const typename List<T1>::Cons _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1, n_});
                          }},
                      l->v());
                }
              },
              [&](_Call1 _f) {
                _result = List<T1>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>> poly_drop(const unsigned int n,
                                             std::shared_ptr<List<T1>> l) {
    std::shared_ptr<List<T1>> _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        {
          _result = std::move(_loop_l);
          _continue = false;
        }
      } else {
        unsigned int n_ = _loop_n - 1;
        std::visit(Overloaded{[&](const typename List<T1>::Nil _args) {
                                _result = List<T1>::ctor::Nil_();
                                _continue = false;
                              },
                              [&](const typename List<T1>::Cons _args) {
                                std::shared_ptr<List<T1>> _next_l = _args.d_a1;
                                unsigned int _next_n = std::move(n_);
                                _loop_l = std::move(_next_l);
                                _loop_n = std::move(_next_n);
                              }},
                   _loop_l->v());
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static std::optional<T1>
  poly_nth(const unsigned int n, const std::shared_ptr<List<T1>> &l) {
    std::optional<T1> _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{[&](const typename List<T1>::Nil _args) {
                       _result = std::nullopt;
                       _continue = false;
                     },
                     [&](const typename List<T1>::Cons _args) {
                       if (_loop_n == 0u) {
                         _result = std::make_optional<T1>(_args.d_a0);
                         _continue = false;
                       } else {
                         std::shared_ptr<List<T1>> _next_l = _args.d_a1;
                         unsigned int _next_n =
                             (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                         _loop_l = std::move(_next_l);
                         _loop_n = std::move(_next_n);
                       }
                     }},
          _loop_l->v());
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  static std::shared_ptr<List<T1>>
  poly_filter(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<T1>::Cons &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = List<T1>::ctor::Nil_();
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _stack.push_back(_Enter{_args.d_a1});
                          }
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = List<T1>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<List<T2>>
  poly_map(F0 &&f, const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      T2 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = List<T2>::ctor::Nil_();
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{f(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = List<T2>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2>
  static std::shared_ptr<List<std::pair<T1, T2>>>
  poly_zip(const std::shared_ptr<List<T1>> &l1,
           const std::shared_ptr<List<T2>> &l2) {
    struct _Enter {
      const std::shared_ptr<List<T2>> l2;
      const std::shared_ptr<List<T1>> l1;
    };

    struct _Call1 {
      decltype(std::make_pair(
          std::declval<const typename List<T1>::Cons &>().d_a0,
          std::declval<const typename List<T2>::Cons &>().d_a0)) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<std::pair<T1, T2>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l2, l1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T2>> l2 = _f.l2;
                const std::shared_ptr<List<T1>> l1 = _f.l1;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = List<std::pair<T1, T2>>::ctor::Nil_();
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<T2>::Nil _args0)
                                      -> void {
                                    _result =
                                        List<std::pair<T1, T2>>::ctor::Nil_();
                                  },
                                  [&](const typename List<T2>::Cons _args0)
                                      -> void {
                                    _stack.push_back(_Call1{std::make_pair(
                                        _args.d_a0, _args0.d_a0)});
                                    _stack.push_back(
                                        _Enter{_args0.d_a1, _args.d_a1});
                                  }},
                              l2->v());
                        }},
                    l1->v());
              },
              [&](_Call1 _f) {
                _result = List<std::pair<T1, T2>>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T2>>>
  poly_unzip(const std::shared_ptr<List<std::pair<T1, T2>>> &l) {
    struct _Enter {
      const std::shared_ptr<List<std::pair<T1, T2>>> l;
    };

    struct _Call1 {
      T2 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T2>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<std::pair<T1, T2>>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<std::pair<T1, T2>>::Nil _args)
                            -> void {
                          _result = std::make_pair(List<T1>::ctor::Nil_(),
                                                   List<T2>::ctor::Nil_());
                        },
                        [&](const typename List<std::pair<T1, T2>>::Cons _args)
                            -> void {
                          T1 a = _args.d_a0.first;
                          T2 b = _args.d_a0.second;
                          _stack.push_back(_Call1{b, a});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                T2 b = _f._s0;
                T1 a = _f._s1;
                std::shared_ptr<List<T1>> as_ = _result.first;
                std::shared_ptr<List<T2>> bs = _result.second;
                _result = std::make_pair(List<T1>::ctor::Cons_(a, as_),
                                         List<T2>::ctor::Cons_(b, bs));
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>>
  poly_partition(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      F0 _s0;
      const typename List<T1>::Cons _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args) -> void {
                          _result = std::make_pair(List<T1>::ctor::Nil_(),
                                                   List<T1>::ctor::Nil_());
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{p, _args});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                F0 p = _f._s0;
                const typename List<T1>::Cons _args = _f._s1;
                std::shared_ptr<List<T1>> trues = _result.first;
                std::shared_ptr<List<T1>> falses = _result.second;
                if (p(_args.d_a0)) {
                  _result = std::make_pair(
                      List<T1>::ctor::Cons_(_args.d_a0, trues), falses);
                } else {
                  _result = std::make_pair(
                      trues, List<T1>::ctor::Cons_(_args.d_a0, falses));
                }
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bool
  poly_member(F0 &&eq, const T1 x, const std::shared_ptr<List<T1>> &l) {
    bool _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<T1>::Nil _args) {
                              _result = false;
                              _continue = false;
                            },
                            [&](const typename List<T1>::Cons _args) {
                              if (eq(x, _args.d_a0)) {
                                _result = true;
                                _continue = false;
                              } else {
                                _loop_l = _args.d_a1;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<T1>> poly_replicate(const unsigned int n,
                                                  const T1 x) {
    struct _Enter {
      const unsigned int n;
    };

    struct _Call1 {
      const T1 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(Overloaded{[&](_Enter _f) {
                              const unsigned int n = _f.n;
                              if (n <= 0) {
                                _result = List<T1>::ctor::Nil_();
                              } else {
                                unsigned int n_ = n - 1;
                                _stack.push_back(_Call1{x});
                                _stack.push_back(_Enter{n_});
                              }
                            },
                            [&](_Call1 _f) {
                              _result = List<T1>::ctor::Cons_(_f._s0, _result);
                            }},
                 _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  nat_length(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<List<unsigned int>>
  nat_reverse(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<List<unsigned int>>
  nat_append(const std::shared_ptr<List<unsigned int>> &_x0,
             const std::shared_ptr<List<unsigned int>> &_x1);
  __attribute__((pure)) static std::optional<unsigned int>
  nat_last(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<List<unsigned int>>
  nat_take(const unsigned int _x0,
           const std::shared_ptr<List<unsigned int>> &_x1);
  static std::shared_ptr<List<unsigned int>>
  nat_drop(const unsigned int _x0,
           const std::shared_ptr<List<unsigned int>> &_x1);
  __attribute__((pure)) static std::optional<unsigned int>
  nat_nth(const unsigned int _x0,
          const std::shared_ptr<List<unsigned int>> &_x1);
  __attribute__((pure)) static bool nat_eq(const unsigned int _x0,
                                           const unsigned int _x1);
  __attribute__((pure)) static bool is_even(const unsigned int x);

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  nat_filter(F0 &&_x0, const std::shared_ptr<List<unsigned int>> &_x1) {
    return poly_filter<unsigned int>(_x0, _x1);
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  nat_map(F0 &&_x0, const std::shared_ptr<List<unsigned int>> &_x1) {
    return poly_map<unsigned int, unsigned int>(_x0, _x1);
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  nat_partition(F0 &&_x0, const std::shared_ptr<List<unsigned int>> &_x1) {
    return poly_partition<unsigned int>(_x0, _x1);
  }

  __attribute__((pure)) static bool
  nat_member(const unsigned int _x0,
             const std::shared_ptr<List<unsigned int>> &_x1);
  static std::shared_ptr<List<unsigned int>>
  nat_replicate(const unsigned int _x0, const unsigned int _x1);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
