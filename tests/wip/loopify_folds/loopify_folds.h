#ifndef INCLUDED_LOOPIFY_FOLDS
#define INCLUDED_LOOPIFY_FOLDS

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

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const List *_self = _f._self;
                       std::visit(
                           Overloaded{[&](const typename List<t_A>::Nil _args)
                                          -> unsigned int {
                                        _result = 0u;
                                        return {};
                                      },
                                      [&](const typename List<t_A>::Cons _args)
                                          -> unsigned int {
                                        _stack.push_back(_Call1{});
                                        _stack.push_back(
                                            _Enter{_args.d_a1.get()});
                                        return {};
                                      }},
                           _self->v());
                     },
                     [&](_Call1 _f) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }
};

struct LoopifyFolds {
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_left(F0 &&f, const unsigned int acc,
            const std::shared_ptr<List<unsigned int>> &l) {
    unsigned int _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = std::move(_loop_acc);
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  _args.d_a1;
                              unsigned int _next_acc =
                                  f(std::move(_loop_acc), _args.d_a0);
                              _loop_l = std::move(_next_l);
                              _loop_acc = std::move(_next_acc);
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_right(F0 &&f, const std::shared_ptr<List<unsigned int>> &l,
             const unsigned int acc) {
    struct _Enter {
      const unsigned int acc;
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{acc, l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const unsigned int acc = _f.acc;
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> unsigned int {
                          _result = std::move(acc);
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> unsigned int {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{std::move(acc), _args.d_a1});
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanl(F0 &&f, const unsigned int acc,
        const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
      const unsigned int acc;
    };

    struct _Call1 {
      const unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                const unsigned int acc = _f.acc;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Cons_(
                              std::move(acc), List<unsigned int>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _stack.push_back(_Call1{acc});
                          _stack.push_back(
                              _Enter{_args.d_a1, f(acc, _args.d_a0)});
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanr(F0 &&f, const unsigned int acc,
        const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const unsigned int _s0;
      F0 _s1;
      const typename List<unsigned int>::Cons _s2;
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
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Cons_(
                              std::move(acc), List<unsigned int>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _stack.push_back(_Call1{acc, f, _args});
                          _stack.push_back(_Enter{_args.d_a1});
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const unsigned int acc = _f._s0;
                F0 f = _f._s1;
                const typename List<unsigned int>::Cons _args = _f._s2;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args0)
                            -> void {
                          _result = List<unsigned int>::ctor::Cons_(
                              std::move(acc), List<unsigned int>::ctor::Nil_());
                        },
                        [&](const typename List<unsigned int>::Cons _args0)
                            -> void {
                          _result = List<unsigned int>::ctor::Cons_(
                              f(_args.d_a0, _args0.d_a0), _args0.d_a1);
                        }},
                    _result->v());
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  foldl1_fuel(const unsigned int fuel, F1 &&f,
              const std::shared_ptr<List<unsigned int>> &l) {
    unsigned int _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          _result = 0u;
          _continue = false;
        }
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        std::visit(
            Overloaded{
                [&](const typename List<unsigned int>::Nil _args) {
                  _result = 0u;
                  _continue = false;
                },
                [&](const typename List<unsigned int>::Cons _args) {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args0) {
                            _result = _args.d_a0;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args0) {
                            std::shared_ptr<List<unsigned int>> _next_l =
                                List<unsigned int>::ctor::Cons_(
                                    f(_args.d_a0, _args0.d_a0), _args0.d_a1);
                            unsigned int _next_fuel = fuel_;
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
                          }},
                      _args.d_a1->v());
                }},
            _loop_l->v());
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldl1(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    return foldl1_fuel(l->length(), f, l);
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldr1(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
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
                        [&](const typename List<unsigned int>::Nil _args)
                            -> unsigned int {
                          _result = 0u;
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> unsigned int {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> unsigned int {
                                    _result = _args.d_a0;
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> unsigned int {
                                    _stack.push_back(_Call1{_args.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((
      pure)) static std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>
  map_accum(F0 &&f, const unsigned int acc,
            const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
      const unsigned int acc;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<unsigned int, std::shared_ptr<List<unsigned int>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                const unsigned int acc = _f.acc;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::pair<unsigned int,
                                         std::shared_ptr<List<unsigned int>>> {
                          _result = std::make_pair(
                              std::move(acc), List<unsigned int>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::pair<unsigned int,
                                         std::shared_ptr<List<unsigned int>>> {
                          unsigned int acc_ = f(acc, _args.d_a0).first;
                          unsigned int y = f(acc, _args.d_a0).second;
                          _stack.push_back(_Call1{y});
                          _stack.push_back(_Enter{_args.d_a1, acc_});
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                unsigned int y = _f._s0;
                unsigned int final_acc = _result.first;
                std::shared_ptr<List<unsigned int>> ys = _result.second;
                _result = std::make_pair(
                    final_acc, List<unsigned int>::ctor::Cons_(y, ys));
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  iterate_accum(F0 &&f, const unsigned int n, const unsigned int x) {
    struct _Enter {
      const unsigned int x;
      const unsigned int n;
    };

    struct _Call1 {
      const unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{x, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(Overloaded{[&](_Enter _f) {
                              const unsigned int x = _f.x;
                              const unsigned int n = _f.n;
                              if (n <= 0) {
                                _result = List<unsigned int>::ctor::Nil_();
                              } else {
                                unsigned int n_ = n - 1;
                                _stack.push_back(_Call1{x});
                                _stack.push_back(_Enter{f(x), std::move(n_)});
                              }
                            },
                            [&](_Call1 _f) {
                              _result = List<unsigned int>::ctor::Cons_(
                                  _f._s0, _result);
                            }},
                 _frame);
    }
    return _result;
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  unfold_fuel(const unsigned int fuel, F1 &&f, const unsigned int seed) {
    struct _Enter {
      const unsigned int seed;
      const unsigned int fuel;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{seed, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(Overloaded{[&](_Enter _f) {
                              const unsigned int seed = _f.seed;
                              const unsigned int fuel = _f.fuel;
                              if (fuel <= 0) {
                                _result = List<unsigned int>::ctor::Nil_();
                              } else {
                                unsigned int fuel_ = fuel - 1;
                                unsigned int x = f(seed).first;
                                unsigned int next_seed = f(seed).second;
                                _stack.push_back(_Call1{x});
                                _stack.push_back(_Enter{next_seed, fuel_});
                              }
                            },
                            [&](_Call1 _f) {
                              _result = List<unsigned int>::ctor::Cons_(
                                  _f._s0, _result);
                            }},
                 _frame);
    }
    return _result;
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  unfold(const unsigned int _x0, F1 &&_x1, const unsigned int _x2) {
    return unfold_fuel(_x0, _x1, _x2);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
