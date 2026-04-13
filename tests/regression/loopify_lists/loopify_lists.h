#ifndef INCLUDED_LOOPIFY_LISTS
#define INCLUDED_LOOPIFY_LISTS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
struct LoopifyLists {
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

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil &) -> void {
                          _result = f;
                        },
                        [&](const typename list<T1>::Cons &_args) -> void {
                          _stack.emplace_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a1});
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
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil &) -> void {
                          _result = f;
                        },
                        [&](const typename list<T1>::Cons &_args) -> void {
                          _stack.emplace_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2.
  template <typename T1>
  static std::shared_ptr<list<T1>> stutter(const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                      list<T1>::nil();
                } else {
                  _head = list<T1>::nil();
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                auto _cell = list<T1>::cons(_args.d_a0, nullptr);
                auto _cell1 = list<T1>::cons(_args.d_a0, nullptr);
                std::get<typename list<T1>::Cons>(_cell->v_mut()).d_a1 = _cell1;
                if (_last) {
                  std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell1;
                _loop_l = _args.d_a1;
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// snoc l x appends x at the end (reverse cons).
  template <typename T1>
  static std::shared_ptr<list<T1>> snoc(const std::shared_ptr<list<T1>> &l,
                                        const T1 x) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                      list<T1>::cons(x, list<T1>::nil());
                } else {
                  _head = list<T1>::cons(x, list<T1>::nil());
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                auto _cell = list<T1>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// intersperse sep l inserts separator between elements.
  template <typename T1>
  static std::shared_ptr<list<T1>>
  intersperse(const T1 sep, const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                      list<T1>::nil();
                } else {
                  _head = list<T1>::nil();
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil &) {
                          if (_last) {
                            std::get<typename list<T1>::Cons>(_last->v_mut())
                                .d_a1 =
                                list<T1>::cons(_args.d_a0, list<T1>::nil());
                          } else {
                            _head = list<T1>::cons(_args.d_a0, list<T1>::nil());
                          }
                          _continue = false;
                        },
                        [&](const typename list<T1>::Cons &) {
                          auto _cell = list<T1>::cons(_args.d_a0, nullptr);
                          auto _cell1 = list<T1>::cons(sep, nullptr);
                          std::get<typename list<T1>::Cons>(_cell->v_mut())
                              .d_a1 = _cell1;
                          if (_last) {
                            std::get<typename list<T1>::Cons>(_last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell1;
                          _loop_l = _args.d_a1;
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
    return _head;
  } /// replicate n x creates n copies of x.

  template <typename T1>
  static std::shared_ptr<list<T1>> replicate(const unsigned int n, const T1 x) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> _last{};
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        {
          if (_last) {
            std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                list<T1>::nil();
          } else {
            _head = list<T1>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int m = _loop_n - 1;
        {
          auto _cell = list<T1>::cons(x, nullptr);
          if (_last) {
            std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_n = m;
          continue;
        }
      }
    }
    return _head;
  }

  /// replicate_list n l repeats list l n times.
  template <typename T1>
  static std::shared_ptr<list<T1>>
  replicate_list(const unsigned int n, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const unsigned int n;
    };

    struct _Call1 {
      const std::shared_ptr<list<T1>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const unsigned int n = _f.n;
                std::function<std::shared_ptr<list<T1>>(
                    std::shared_ptr<list<T1>>, std::shared_ptr<list<T1>>)>
                    app;
                app = [&](std::shared_ptr<list<T1>> l1,
                          std::shared_ptr<list<T1>> l2)
                    -> std::shared_ptr<list<T1>> {
                  struct _Enter {
                    std::shared_ptr<list<T1>> l1;
                  };
                  struct _Call1 {
                    decltype(std::declval<const typename list<T1>::Cons &>()
                                 .d_a0) _s0;
                  };
                  using _Frame = std::variant<_Enter, _Call1>;
                  std::shared_ptr<list<T1>> _result{};
                  std::vector<_Frame> _stack;
                  _stack.emplace_back(_Enter{l1});
                  while (!_stack.empty()) {
                    _Frame _frame = std::move(_stack.back());
                    _stack.pop_back();
                    std::visit(
                        Overloaded{
                            [&](_Enter _f) {
                              std::shared_ptr<list<T1>> l1 = _f.l1;
                              std::visit(
                                  Overloaded{
                                      [&](const typename list<T1>::Nil &)
                                          -> void { _result = std::move(l2); },
                                      [&](const typename list<T1>::Cons &_args)
                                          -> void {
                                        _stack.emplace_back(_Call1{_args.d_a0});
                                        _stack.emplace_back(_Enter{_args.d_a1});
                                      }},
                                  l1->v());
                            },
                            [&](_Call1 _f) {
                              _result = list<T1>::cons(_f._s0, _result);
                            }},
                        _frame);
                  }
                  return _result;
                };
                if (n <= 0) {
                  _result = list<T1>::nil();
                } else {
                  unsigned int m = n - 1;
                  _stack.emplace_back(_Call1{l});
                  _stack.emplace_back(_Enter{m});
                }
              },
              [&](_Call1 _f) { _result = app(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// init_list n f generates f 0, f 1, ..., f (n-1).
  template <typename T1, MapsTo<T1, unsigned int> F1>
  static std::shared_ptr<list<T1>> init_list(const unsigned int n, F1 &&f) {
    std::function<std::shared_ptr<list<T1>>(unsigned int)> go;
    go = [&](unsigned int i) -> std::shared_ptr<list<T1>> {
      struct _Enter {
        unsigned int i;
      };
      struct _Call1 {
        decltype(f((((n - std::declval<unsigned int &>()) > n
                         ? 0
                         : (n - std::declval<unsigned int &>()))))) _s0;
      };
      using _Frame = std::variant<_Enter, _Call1>;
      std::shared_ptr<list<T1>> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{i});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(Overloaded{[&](_Enter _f) {
                                unsigned int i = _f.i;
                                if (i <= 0) {
                                  _result = list<T1>::nil();
                                } else {
                                  unsigned int j = i - 1;
                                  _stack.emplace_back(
                                      _Call1{f((((n - i) > n ? 0 : (n - i))))});
                                  _stack.emplace_back(_Enter{j});
                                }
                              },
                              [&](_Call1 _f) {
                                _result = list<T1>::cons(_f._s0, _result);
                              }},
                   _frame);
      }
      return _result;
    };
    return go(n);
  }

  /// range start count generates start, start+1, ..., start+count-1.
  static std::shared_ptr<list<unsigned int>> range(const unsigned int start,
                                                   const unsigned int count0);

  /// tails l returns all suffixes.
  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  tails(std::shared_ptr<list<T1>> l) {
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _head{};
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = list<std::shared_ptr<list<T1>>>::cons(
                      list<T1>::nil(), list<std::shared_ptr<list<T1>>>::nil());
                } else {
                  _head = list<std::shared_ptr<list<T1>>>::cons(
                      list<T1>::nil(), list<std::shared_ptr<list<T1>>>::nil());
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                auto _cell =
                    list<std::shared_ptr<list<T1>>>::cons(_loop_l, nullptr);
                if (_last) {
                  std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// inits l returns all prefixes (complex recursion pattern).
  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  inits(const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(list<T1>::nil()) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil &) -> void {
                          _result = list<std::shared_ptr<list<T1>>>::cons(
                              list<T1>::nil(),
                              list<std::shared_ptr<list<T1>>>::nil());
                        },
                        [&](const typename list<T1>::Cons &_args) -> void {
                          std::function<std::shared_ptr<
                              list<std::shared_ptr<list<T1>>>>(
                              std::shared_ptr<list<std::shared_ptr<list<T1>>>>)>
                              map_cons;
                          map_cons = [&](std::shared_ptr<
                                         list<std::shared_ptr<list<T1>>>>
                                             ys)
                              -> std::shared_ptr<
                                  list<std::shared_ptr<list<T1>>>> {
                            struct _Enter {
                              std::shared_ptr<list<std::shared_ptr<list<T1>>>>
                                  ys;
                            };
                            struct _Call1 {
                              decltype(list<T1>::cons(
                                  std::declval<const typename list<
                                      std::shared_ptr<list<T1>>>::Cons &>()
                                      .d_a0,
                                  std::declval<const typename list<
                                      std::shared_ptr<list<T1>>>::Cons &>()
                                      .d_a0)) _s0;
                            };
                            using _Frame = std::variant<_Enter, _Call1>;
                            std::shared_ptr<list<std::shared_ptr<list<T1>>>>
                                _result{};
                            std::vector<_Frame> _stack;
                            _stack.emplace_back(_Enter{ys});
                            while (!_stack.empty()) {
                              _Frame _frame = std::move(_stack.back());
                              _stack.pop_back();
                              std::visit(
                                  Overloaded{
                                      [&](_Enter _f) {
                                        std::shared_ptr<
                                            list<std::shared_ptr<list<T1>>>>
                                            ys = _f.ys;
                                        std::visit(
                                            Overloaded{
                                                [&](const typename list<
                                                    std::shared_ptr<list<T1>>>::
                                                        Nil &) -> void {
                                                  _result =
                                                      list<std::shared_ptr<
                                                          list<T1>>>::nil();
                                                },
                                                [&](const typename list<
                                                    std::shared_ptr<list<T1>>>::
                                                        Cons &_args) -> void {
                                                  _stack.emplace_back(
                                                      _Call1{list<T1>::cons(
                                                          _args.d_a0,
                                                          _args.d_a0)});
                                                  _stack.emplace_back(
                                                      _Enter{_args.d_a1});
                                                }},
                                            ys->v());
                                      },
                                      [&](_Call1 _f) {
                                        _result =
                                            list<std::shared_ptr<list<T1>>>::
                                                cons(_f._s0, _result);
                                      }},
                                  _frame);
                            }
                            return _result;
                          };
                          _stack.emplace_back(_Call1{list<T1>::nil()});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = list<std::shared_ptr<list<T1>>>::cons(
                    _f._s0, map_cons(_result));
              }},
          _frame);
    }
    return _result;
  }

  /// scanl f acc l returns intermediate fold results.
  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  static std::shared_ptr<list<T2>> scanl(F0 &&f, const T2 acc,
                                         const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<T2>> _head{};
    std::shared_ptr<list<T2>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    T2 _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T2>::Cons>(_last->v_mut()).d_a1 =
                      list<T2>::cons(_loop_acc, list<T2>::nil());
                } else {
                  _head = list<T2>::cons(_loop_acc, list<T2>::nil());
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                T2 new_acc = f(_loop_acc, _args.d_a0);
                auto _cell = list<T2>::cons(_loop_acc, nullptr);
                if (_last) {
                  std::get<typename list<T2>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<list<T1>> _next_l = _args.d_a1;
                T2 _next_acc = new_acc;
                _loop_l = std::move(_next_l);
                _loop_acc = std::move(_next_acc);
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// group_by eq l groups consecutive equal elements.
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  group_by_aux(F0 &&eq, const T1 prev, std::shared_ptr<list<T1>> acc,
               const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _head{};
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    std::shared_ptr<list<T1>> _loop_acc = acc;
    T1 _loop_prev = prev;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = list<std::shared_ptr<list<T1>>>::cons(
                      _loop_acc, list<std::shared_ptr<list<T1>>>::nil());
                } else {
                  _head = list<std::shared_ptr<list<T1>>>::cons(
                      _loop_acc, list<std::shared_ptr<list<T1>>>::nil());
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                if (eq(_loop_prev, _args.d_a0)) {
                  std::shared_ptr<list<T1>> _next_l = _args.d_a1;
                  std::shared_ptr<list<T1>> _next_acc =
                      list<T1>::cons(_args.d_a0, _loop_acc);
                  T1 _next_prev = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_acc = std::move(_next_acc);
                  _loop_prev = std::move(_next_prev);
                } else {
                  auto _cell =
                      list<std::shared_ptr<list<T1>>>::cons(_loop_acc, nullptr);
                  if (_last) {
                    std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                        _last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  std::shared_ptr<list<T1>> _next_l = _args.d_a1;
                  std::shared_ptr<list<T1>> _next_acc =
                      list<T1>::cons(_args.d_a0, list<T1>::nil());
                  T1 _next_prev = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_acc = std::move(_next_acc);
                  _loop_prev = std::move(_next_prev);
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  group_by(F0 &&eq, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename list<T1>::Nil &)
                       -> std::shared_ptr<list<std::shared_ptr<list<T1>>>> {
                     return list<std::shared_ptr<list<T1>>>::nil();
                   },
                   [&](const typename list<T1>::Cons &_args)
                       -> std::shared_ptr<list<std::shared_ptr<list<T1>>>> {
                     return group_by_aux<T1>(
                         eq, _args.d_a0,
                         list<T1>::cons(_args.d_a0, list<T1>::nil()),
                         _args.d_a1);
                   }},
        l->v());
  } /// chunks_of n l splits into chunks of size n.

  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  chunks_of_aux(const unsigned int n, const std::shared_ptr<list<T1>> &l,
                const unsigned int fuel) {
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _head{};
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _last{};
    unsigned int _loop_fuel = fuel;
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                _last->v_mut())
                .d_a1 = list<std::shared_ptr<list<T1>>>::nil();
          } else {
            _head = list<std::shared_ptr<list<T1>>>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int f = _loop_fuel - 1;
        std::function<std::shared_ptr<list<T1>>(unsigned int,
                                                std::shared_ptr<list<T1>>)>
            take;
        take = [&](unsigned int k,
                   std::shared_ptr<list<T1>> lst) -> std::shared_ptr<list<T1>> {
          struct _Enter {
            std::shared_ptr<list<T1>> lst;
            unsigned int k;
          };
          struct _Call1 {
            decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          std::shared_ptr<list<T1>> _result{};
          std::vector<_Frame> _stack;
          _stack.emplace_back(_Enter{lst, k});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            std::visit(
                Overloaded{
                    [&](_Enter _f) {
                      std::shared_ptr<list<T1>> lst = _f.lst;
                      unsigned int k = _f.k;
                      if (k <= 0) {
                        _result = list<T1>::nil();
                      } else {
                        unsigned int m = k - 1;
                        std::visit(
                            Overloaded{
                                [&](const typename list<T1>::Nil &) -> void {
                                  _result = list<T1>::nil();
                                },
                                [&](const typename list<T1>::Cons &_args)
                                    -> void {
                                  _stack.emplace_back(_Call1{_args.d_a0});
                                  _stack.emplace_back(_Enter{_args.d_a1, m});
                                }},
                            lst->v());
                      }
                    },
                    [&](_Call1 _f) {
                      _result = list<T1>::cons(_f._s0, _result);
                    }},
                _frame);
          }
          return _result;
        };
        std::function<std::shared_ptr<list<T1>>(unsigned int,
                                                std::shared_ptr<list<T1>>)>
            drop0;
        drop0 = [](unsigned int k,
                   std::shared_ptr<list<T1>> lst) -> std::shared_ptr<list<T1>> {
          std::shared_ptr<list<T1>> _result;
          std::shared_ptr<list<T1>> _loop_lst = lst;
          unsigned int _loop_k = k;
          bool _continue = true;
          while (_continue) {
            if (_loop_k <= 0) {
              {
                _result = std::move(_loop_lst);
                _continue = false;
              }
            } else {
              unsigned int m = _loop_k - 1;
              std::visit(Overloaded{[&](const typename list<T1>::Nil &) {
                                      _result = list<T1>::nil();
                                      _continue = false;
                                    },
                                    [&](const typename list<T1>::Cons &_args0) {
                                      std::shared_ptr<list<T1>> _next_lst =
                                          _args0.d_a1;
                                      unsigned int _next_k = m;
                                      _loop_lst = std::move(_next_lst);
                                      _loop_k = std::move(_next_k);
                                    }},
                         _loop_lst->v());
            }
          }
          return _result;
        };
        std::visit(
            Overloaded{
                [&](const typename list<T1>::Nil &) {
                  if (_last) {
                    std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                        _last->v_mut())
                        .d_a1 = list<std::shared_ptr<list<T1>>>::nil();
                  } else {
                    _head = list<std::shared_ptr<list<T1>>>::nil();
                  }
                  _continue = false;
                },
                [&](const typename list<T1>::Cons &) {
                  std::shared_ptr<list<T1>> chunk = take(n, _loop_l);
                  std::shared_ptr<list<T1>> rest = drop0(n, _loop_l);
                  std::visit(
                      Overloaded{[&](const typename list<T1>::Nil &) {
                                   if (_last) {
                                     std::get<typename list<
                                         std::shared_ptr<list<T1>>>::Cons>(
                                         _last->v_mut())
                                         .d_a1 =
                                         list<std::shared_ptr<list<T1>>>::nil();
                                   } else {
                                     _head =
                                         list<std::shared_ptr<list<T1>>>::nil();
                                   }
                                   _continue = false;
                                 },
                                 [&](const typename list<T1>::Cons &) {
                                   auto _cell =
                                       list<std::shared_ptr<list<T1>>>::cons(
                                           chunk, nullptr);
                                   if (_last) {
                                     std::get<typename list<
                                         std::shared_ptr<list<T1>>>::Cons>(
                                         _last->v_mut())
                                         .d_a1 = _cell;
                                   } else {
                                     _head = _cell;
                                   }
                                   _last = _cell;
                                   unsigned int _next_fuel = f;
                                   std::shared_ptr<list<T1>> _next_l = rest;
                                   _loop_fuel = std::move(_next_fuel);
                                   _loop_l = std::move(_next_l);
                                 }},
                      chunk->v());
                }},
            _loop_l->v());
      }
    }
    return _head;
  }

  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  chunks_of(const unsigned int n, const std::shared_ptr<list<T1>> &l) {
    std::function<unsigned int(std::shared_ptr<list<T1>>)> length;
    length = [&](std::shared_ptr<list<T1>> l0) -> unsigned int {
      struct _Enter {
        std::shared_ptr<list<T1>> l0;
      };
      struct _Call1 {};
      using _Frame = std::variant<_Enter, _Call1>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{l0});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  std::shared_ptr<list<T1>> l0 = _f.l0;
                  std::visit(
                      Overloaded{
                          [&](const typename list<T1>::Nil &) -> void {
                            _result = 0u;
                          },
                          [&](const typename list<T1>::Cons &_args) -> void {
                            _stack.emplace_back(_Call1{});
                            _stack.emplace_back(_Enter{_args.d_a1});
                          }},
                      l0->v());
                },
                [&](_Call1) { _result = (_result + 1); }},
            _frame);
      }
      return _result;
    };
    return chunks_of_aux<T1>(n, l, (length(l) + 1));
  }

  /// step_sum l sums with conditional contributions: even values as-is, odd
  /// doubled.
  __attribute__((pure)) static unsigned int
  step_sum(const std::shared_ptr<list<unsigned int>> &l);
  /// sum_abs l sums absolute values (using monus for nat).
  __attribute__((pure)) static unsigned int
  sum_abs(const std::shared_ptr<list<unsigned int>> &l,
          const unsigned int base);
  /// four_elem l multi-case pattern matching on list structure.
  __attribute__((pure)) static unsigned int
  four_elem(const std::shared_ptr<list<unsigned int>> &l);
  /// between lo hi l filters elements in range lo, hi.
  static std::shared_ptr<list<unsigned int>>
  between(const unsigned int lo, const unsigned int hi,
          const std::shared_ptr<list<unsigned int>> &l);

  /// count_matching p l counts elements satisfying predicate.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  count_matching(F0 &&p, const std::shared_ptr<list<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename list<unsigned int>::Cons &_args)
                            -> void {
                          if (p(_args.d_a0)) {
                            _stack.emplace_back(_Call1{});
                            _stack.emplace_back(_Enter{_args.d_a1});
                          } else {
                            _stack.emplace_back(_Enter{_args.d_a1});
                          }
                        }},
                    l->v());
              },
              [&](_Call1) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }

  /// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
  __attribute__((pure)) static unsigned int
  categorize(const unsigned int k,
             const std::shared_ptr<list<unsigned int>> &l);
  /// max_prefix_sum l maximum prefix sum (Kadane-like).
  __attribute__((pure)) static unsigned int
  max_prefix_sum(const std::shared_ptr<list<unsigned int>> &l);
  /// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
  static std::shared_ptr<list<unsigned int>>
  pairwise_sum(const std::shared_ptr<list<unsigned int>> &l);
  /// weighted_sum i l weighted sum with increasing weights.
  __attribute__((pure)) static unsigned int
  weighted_sum(const unsigned int i,
               const std::shared_ptr<list<unsigned int>> &l);

  /// zip_with f l1 l2 zips two lists with a function.
  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static std::shared_ptr<list<T3>>
  zip_with(F0 &&f, const std::shared_ptr<list<T1>> &l1,
           const std::shared_ptr<list<T2>> &l2) {
    std::shared_ptr<list<T3>> _head{};
    std::shared_ptr<list<T3>> _last{};
    std::shared_ptr<list<T2>> _loop_l2 = l2;
    std::shared_ptr<list<T1>> _loop_l1 = l1;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T3>::Cons>(_last->v_mut()).d_a1 =
                      list<T3>::nil();
                } else {
                  _head = list<T3>::nil();
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename list<T2>::Nil &) {
                          if (_last) {
                            std::get<typename list<T3>::Cons>(_last->v_mut())
                                .d_a1 = list<T3>::nil();
                          } else {
                            _head = list<T3>::nil();
                          }
                          _continue = false;
                        },
                        [&](const typename list<T2>::Cons &_args0) {
                          auto _cell = list<T3>::cons(
                              f(_args.d_a0, _args0.d_a0), nullptr);
                          if (_last) {
                            std::get<typename list<T3>::Cons>(_last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          std::shared_ptr<list<T2>> _next_l2 = _args0.d_a1;
                          std::shared_ptr<list<T1>> _next_l1 = _args.d_a1;
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        }},
                    _loop_l2->v());
              }},
          _loop_l1->v());
    }
    return _head;
  }

  /// zip_longest l1 l2 def zips with default for mismatched lengths.
  template <typename T1>
  static std::shared_ptr<list<std::pair<T1, T1>>>
  zip_longest_aux(const unsigned int fuel, const std::shared_ptr<list<T1>> &l1,
                  const std::shared_ptr<list<T1>> &l2, const T1 default0) {
    std::shared_ptr<list<std::pair<T1, T1>>> _head{};
    std::shared_ptr<list<std::pair<T1, T1>>> _last{};
    std::shared_ptr<list<T1>> _loop_l2 = l2;
    std::shared_ptr<list<T1>> _loop_l1 = l1;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename list<std::pair<T1, T1>>::Cons>(_last->v_mut())
                .d_a1 = list<std::pair<T1, T1>>::nil();
          } else {
            _head = list<std::pair<T1, T1>>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int f = _loop_fuel - 1;
        std::visit(
            Overloaded{
                [&](const typename list<T1>::Nil &) {
                  std::visit(
                      Overloaded{
                          [&](const typename list<T1>::Nil &) {
                            if (_last) {
                              std::get<typename list<std::pair<T1, T1>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = list<std::pair<T1, T1>>::nil();
                            } else {
                              _head = list<std::pair<T1, T1>>::nil();
                            }
                            _continue = false;
                          },
                          [&](const typename list<T1>::Cons &_args0) {
                            auto _cell = list<std::pair<T1, T1>>::cons(
                                std::make_pair(default0, _args0.d_a0), nullptr);
                            if (_last) {
                              std::get<typename list<std::pair<T1, T1>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<list<T1>> _next_l2 = _args0.d_a1;
                            std::shared_ptr<list<T1>> _next_l1 =
                                list<T1>::nil();
                            unsigned int _next_fuel = f;
                            _loop_l2 = std::move(_next_l2);
                            _loop_l1 = std::move(_next_l1);
                            _loop_fuel = std::move(_next_fuel);
                          }},
                      _loop_l2->v());
                },
                [&](const typename list<T1>::Cons &_args) {
                  std::visit(
                      Overloaded{
                          [&](const typename list<T1>::Nil &) {
                            auto _cell = list<std::pair<T1, T1>>::cons(
                                std::make_pair(_args.d_a0, default0), nullptr);
                            if (_last) {
                              std::get<typename list<std::pair<T1, T1>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<list<T1>> _next_l2 =
                                list<T1>::nil();
                            std::shared_ptr<list<T1>> _next_l1 = _args.d_a1;
                            unsigned int _next_fuel = f;
                            _loop_l2 = std::move(_next_l2);
                            _loop_l1 = std::move(_next_l1);
                            _loop_fuel = std::move(_next_fuel);
                          },
                          [&](const typename list<T1>::Cons &_args0) {
                            auto _cell = list<std::pair<T1, T1>>::cons(
                                std::make_pair(_args.d_a0, _args0.d_a0),
                                nullptr);
                            if (_last) {
                              std::get<typename list<std::pair<T1, T1>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<list<T1>> _next_l2 = _args0.d_a1;
                            std::shared_ptr<list<T1>> _next_l1 = _args.d_a1;
                            unsigned int _next_fuel = f;
                            _loop_l2 = std::move(_next_l2);
                            _loop_l1 = std::move(_next_l1);
                            _loop_fuel = std::move(_next_fuel);
                          }},
                      _loop_l2->v());
                }},
            _loop_l1->v());
      }
    }
    return _head;
  }

  template <typename T1>
  static std::shared_ptr<list<std::pair<T1, T1>>>
  zip_longest(const std::shared_ptr<list<T1>> &l1,
              const std::shared_ptr<list<T1>> &l2, const T1 default0) {
    std::function<unsigned int(std::shared_ptr<list<T1>>)> length;
    length = [&](std::shared_ptr<list<T1>> l) -> unsigned int {
      struct _Enter {
        std::shared_ptr<list<T1>> l;
      };
      struct _Call1 {};
      using _Frame = std::variant<_Enter, _Call1>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{l});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  std::shared_ptr<list<T1>> l = _f.l;
                  std::visit(
                      Overloaded{
                          [&](const typename list<T1>::Nil &) -> void {
                            _result = 0u;
                          },
                          [&](const typename list<T1>::Cons &_args) -> void {
                            _stack.emplace_back(_Call1{});
                            _stack.emplace_back(_Enter{_args.d_a1});
                          }},
                      l->v());
                },
                [&](_Call1) { _result = (_result + 1); }},
            _frame);
      }
      return _result;
    };
    unsigned int len = (length(l1) + length(l2));
    return zip_longest_aux<T1>((len + 1), l1, l2, default0);
  }

  /// sliding_pairs l returns consecutive pairs: 1,2,3 -> (1,2),(2,3).
  template <typename T1>
  static std::shared_ptr<list<std::pair<T1, T1>>>
  sliding_pairs(const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<std::pair<T1, T1>>> _head{};
    std::shared_ptr<list<std::pair<T1, T1>>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<std::pair<T1, T1>>::Cons>(
                      _last->v_mut())
                      .d_a1 = list<std::pair<T1, T1>>::nil();
                } else {
                  _head = list<std::pair<T1, T1>>::nil();
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil &) {
                          if (_last) {
                            std::get<typename list<std::pair<T1, T1>>::Cons>(
                                _last->v_mut())
                                .d_a1 = list<std::pair<T1, T1>>::nil();
                          } else {
                            _head = list<std::pair<T1, T1>>::nil();
                          }
                          _continue = false;
                        },
                        [&](const typename list<T1>::Cons &_args0) {
                          auto _cell = list<std::pair<T1, T1>>::cons(
                              std::make_pair(_args.d_a0, _args0.d_a0), nullptr);
                          if (_last) {
                            std::get<typename list<std::pair<T1, T1>>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          _loop_l = _args.d_a1;
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// partition3 p q l partitions into 3 groups based on 2 predicates.
  template <MapsTo<bool, unsigned int> F0, MapsTo<bool, unsigned int> F1>
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<list<unsigned int>>,
                                        std::shared_ptr<list<unsigned int>>>,
                              std::shared_ptr<list<unsigned int>>>
  partition3(F0 &&p, F1 &&q, const std::shared_ptr<list<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {
      F0 _s0;
      const typename list<unsigned int>::Cons _s1;
      F1 _s2;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::pair<std::shared_ptr<list<unsigned int>>,
                        std::shared_ptr<list<unsigned int>>>,
              std::shared_ptr<list<unsigned int>>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil &) -> void {
                          _result = std::make_pair(
                              std::make_pair(list<unsigned int>::nil(),
                                             list<unsigned int>::nil()),
                              list<unsigned int>::nil());
                        },
                        [&](const typename list<unsigned int>::Cons &_args)
                            -> void {
                          _stack.emplace_back(_Call1{p, _args, q});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                F0 p = _f._s0;
                const typename list<unsigned int>::Cons _args = _f._s1;
                F1 q = _f._s2;
                const std::pair<std::shared_ptr<list<unsigned int>>,
                                std::shared_ptr<list<unsigned int>>> &p0 =
                    _result.first;
                const std::shared_ptr<list<unsigned int>> &cs = _result.second;
                const std::shared_ptr<list<unsigned int>> &as_ = p0.first;
                const std::shared_ptr<list<unsigned int>> &bs = p0.second;
                if (p(_args.d_a0)) {
                  _result = std::make_pair(
                      std::make_pair(list<unsigned int>::cons(_args.d_a0, as_),
                                     bs),
                      cs);
                } else {
                  if (q(_args.d_a0)) {
                    _result = std::make_pair(
                        std::make_pair(
                            as_, list<unsigned int>::cons(_args.d_a0, bs)),
                        cs);
                  } else {
                    _result = std::make_pair(
                        std::make_pair(as_, bs),
                        list<unsigned int>::cons(_args.d_a0, cs));
                  }
                }
              }},
          _frame);
    }
    return _result;
  }

  /// transpose m transposes a matrix (list of lists).
  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  transpose_fuel(const unsigned int fuel,
                 const std::shared_ptr<list<std::shared_ptr<list<T1>>>> &m) {
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _head{};
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _last{};
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _loop_m = m;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                _last->v_mut())
                .d_a1 = list<std::shared_ptr<list<T1>>>::nil();
          } else {
            _head = list<std::shared_ptr<list<T1>>>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int f = _loop_fuel - 1;
        std::function<std::shared_ptr<list<T1>>(
            std::shared_ptr<list<std::shared_ptr<list<T1>>>>)>
            map_head;
        map_head = [&](std::shared_ptr<list<std::shared_ptr<list<T1>>>> l)
            -> std::shared_ptr<list<T1>> {
          struct _Enter {
            std::shared_ptr<list<std::shared_ptr<list<T1>>>> l;
          };
          struct _Call1 {
            decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          std::shared_ptr<list<T1>> _result{};
          std::vector<_Frame> _stack;
          _stack.emplace_back(_Enter{l});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            std::visit(
                Overloaded{
                    [&](_Enter _f) {
                      std::shared_ptr<list<std::shared_ptr<list<T1>>>> l = _f.l;
                      std::visit(
                          Overloaded{
                              [&](const typename list<
                                  std::shared_ptr<list<T1>>>::Nil &) -> void {
                                _result = list<T1>::nil();
                              },
                              [&](const typename list<
                                  std::shared_ptr<list<T1>>>::Cons &_args)
                                  -> void {
                                std::visit(
                                    Overloaded{
                                        [&](const typename list<T1>::Nil &)
                                            -> void {
                                          _result = list<T1>::nil();
                                        },
                                        [&](const typename list<T1>::Cons
                                                &_args0) -> void {
                                          _stack.emplace_back(
                                              _Call1{_args0.d_a0});
                                          _stack.emplace_back(
                                              _Enter{_args.d_a1});
                                        }},
                                    _args.d_a0->v());
                              }},
                          l->v());
                    },
                    [&](_Call1 _f) {
                      _result = list<T1>::cons(_f._s0, _result);
                    }},
                _frame);
          }
          return _result;
        };
        std::function<std::shared_ptr<list<std::shared_ptr<list<T1>>>>(
            std::shared_ptr<list<std::shared_ptr<list<T1>>>>)>
            map_tail;
        map_tail = [&](std::shared_ptr<list<std::shared_ptr<list<T1>>>> l)
            -> std::shared_ptr<list<std::shared_ptr<list<T1>>>> {
          struct _Enter {
            std::shared_ptr<list<std::shared_ptr<list<T1>>>> l;
          };
          struct _Call1 {
            decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          std::shared_ptr<list<std::shared_ptr<list<T1>>>> _result{};
          std::vector<_Frame> _stack;
          _stack.emplace_back(_Enter{l});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            std::visit(
                Overloaded{
                    [&](_Enter _f) {
                      std::shared_ptr<list<std::shared_ptr<list<T1>>>> l = _f.l;
                      std::visit(
                          Overloaded{
                              [&](const typename list<
                                  std::shared_ptr<list<T1>>>::Nil &) -> void {
                                _result =
                                    list<std::shared_ptr<list<T1>>>::nil();
                              },
                              [&](const typename list<
                                  std::shared_ptr<list<T1>>>::Cons &_args0)
                                  -> void {
                                std::visit(
                                    Overloaded{
                                        [&](const typename list<T1>::Nil &)
                                            -> void {
                                          _result = list<
                                              std::shared_ptr<list<T1>>>::nil();
                                        },
                                        [&](const typename list<T1>::Cons
                                                &_args1) -> void {
                                          _stack.emplace_back(
                                              _Call1{_args1.d_a1});
                                          _stack.emplace_back(
                                              _Enter{_args0.d_a1});
                                        }},
                                    _args0.d_a0->v());
                              }},
                          l->v());
                    },
                    [&](_Call1 _f) {
                      _result = list<std::shared_ptr<list<T1>>>::cons(_f._s0,
                                                                      _result);
                    }},
                _frame);
          }
          return _result;
        };
        std::visit(
            Overloaded{
                [&](const typename list<std::shared_ptr<list<T1>>>::Nil &) {
                  if (_last) {
                    std::get<typename list<std::shared_ptr<list<T1>>>::Cons>(
                        _last->v_mut())
                        .d_a1 = list<std::shared_ptr<list<T1>>>::nil();
                  } else {
                    _head = list<std::shared_ptr<list<T1>>>::nil();
                  }
                  _continue = false;
                },
                [&](const typename list<std::shared_ptr<list<T1>>>::Cons
                        &_args1) {
                  std::visit(
                      Overloaded{
                          [&](const typename list<T1>::Nil &) {
                            if (_last) {
                              std::get<typename list<
                                  std::shared_ptr<list<T1>>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 =
                                  list<std::shared_ptr<list<T1>>>::nil();
                            } else {
                              _head = list<std::shared_ptr<list<T1>>>::nil();
                            }
                            _continue = false;
                          },
                          [&](const typename list<T1>::Cons &) {
                            std::shared_ptr<list<T1>> heads = map_head(_loop_m);
                            std::shared_ptr<list<std::shared_ptr<list<T1>>>>
                                tails0 = map_tail(_loop_m);
                            std::visit(
                                Overloaded{
                                    [&](const typename list<T1>::Nil &) {
                                      if (_last) {
                                        std::get<typename list<
                                            std::shared_ptr<list<T1>>>::Cons>(
                                            _last->v_mut())
                                            .d_a1 = list<
                                            std::shared_ptr<list<T1>>>::nil();
                                      } else {
                                        _head = list<
                                            std::shared_ptr<list<T1>>>::nil();
                                      }
                                      _continue = false;
                                    },
                                    [&](const typename list<T1>::Cons &) {
                                      auto _cell =
                                          list<std::shared_ptr<list<T1>>>::cons(
                                              heads, nullptr);
                                      if (_last) {
                                        std::get<typename list<
                                            std::shared_ptr<list<T1>>>::Cons>(
                                            _last->v_mut())
                                            .d_a1 = _cell;
                                      } else {
                                        _head = _cell;
                                      }
                                      _last = _cell;
                                      std::shared_ptr<
                                          list<std::shared_ptr<list<T1>>>>
                                          _next_m = tails0;
                                      unsigned int _next_fuel = f;
                                      _loop_m = std::move(_next_m);
                                      _loop_fuel = std::move(_next_fuel);
                                    }},
                                heads->v());
                          }},
                      _args1.d_a0->v());
                }},
            _loop_m->v());
      }
    }
    return _head;
  }

  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  transpose(const std::shared_ptr<list<std::shared_ptr<list<T1>>>> &m) {
    return transpose_fuel<T1>(100u, m);
  }

  /// map_accum_l f acc l maps with accumulator from left.
  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<T3, std::shared_ptr<list<T2>>>
  map_accum_l(F0 &&f, const T3 acc, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
      const T3 acc;
    };

    struct _Call1 {
      T2 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<T3, std::shared_ptr<list<T2>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                const T3 acc = _f.acc;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil &) -> void {
                          _result = std::make_pair(acc, list<T2>::nil());
                        },
                        [&](const typename list<T1>::Cons &_args) -> void {
                          auto _cs = f(acc, _args.d_a0);
                          const T3 &acc_ = _cs.first;
                          const T2 &y = _cs.second;
                          _stack.emplace_back(_Call1{y});
                          _stack.emplace_back(_Enter{_args.d_a1, acc_});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                T2 y = _f._s0;
                const T3 &acc__ = _result.first;
                const std::shared_ptr<list<T2>> &ys = _result.second;
                _result = std::make_pair(acc__, list<T2>::cons(y, ys));
              }},
          _frame);
    }
    return _result;
  }

  /// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
  static std::shared_ptr<list<unsigned int>>
  prefix_sums(const unsigned int acc,
              const std::shared_ptr<list<unsigned int>> &l);
  /// uniq_sorted l removes consecutive duplicates from sorted list.
  static std::shared_ptr<list<unsigned int>>
  uniq_sorted(const std::shared_ptr<list<unsigned int>> &l);
  /// Helper: take first n elements.
  static std::shared_ptr<list<unsigned int>>
  take_n(const unsigned int n, const std::shared_ptr<list<unsigned int>> &l);
  /// Helper: list length.
  __attribute__((pure)) static unsigned int
  len_list(const std::shared_ptr<list<unsigned int>> &l);
  /// windows n l returns all sliding windows of size n.
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  windows_aux(const unsigned int fuel, const unsigned int n,
              const std::shared_ptr<list<unsigned int>> &l);
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  windows(const unsigned int n, const std::shared_ptr<list<unsigned int>> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  __attribute__((pure)) static bool
  is_prefix_of(const std::shared_ptr<list<unsigned int>> &l1,
               const std::shared_ptr<list<unsigned int>> &l2);
  /// lookup_all key l finds all values for key in association list.
  static std::shared_ptr<list<unsigned int>> lookup_all(
      const unsigned int key,
      const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);

  /// delete_by eq x l deletes first element equal to x by custom equality.
  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<list<unsigned int>>
  delete_by(F0 &&eq, const unsigned int x,
            const std::shared_ptr<list<unsigned int>> &l) {
    std::shared_ptr<list<unsigned int>> _head{};
    std::shared_ptr<list<unsigned int>> _last{};
    std::shared_ptr<list<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = list<unsigned int>::nil();
                } else {
                  _head = list<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename list<unsigned int>::Cons &_args) {
                if (eq(x, _args.d_a0)) {
                  if (_last) {
                    std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _args.d_a1;
                  } else {
                    _head = _args.d_a1;
                  }
                  _continue = false;
                } else {
                  auto _cell = list<unsigned int>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// find_indices p l returns list of indices where predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<list<unsigned int>>
  find_indices_aux(F0 &&p, const std::shared_ptr<list<unsigned int>> &l,
                   const unsigned int i) {
    std::shared_ptr<list<unsigned int>> _head{};
    std::shared_ptr<list<unsigned int>> _last{};
    unsigned int _loop_i = i;
    std::shared_ptr<list<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = list<unsigned int>::nil();
                } else {
                  _head = list<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename list<unsigned int>::Cons &_args) {
                if (p(_args.d_a0)) {
                  auto _cell = list<unsigned int>::cons(_loop_i, nullptr);
                  if (_last) {
                    std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  unsigned int _next_i = (_loop_i + 1);
                  std::shared_ptr<list<unsigned int>> _next_l = _args.d_a1;
                  _loop_i = std::move(_next_i);
                  _loop_l = std::move(_next_l);
                } else {
                  unsigned int _next_i = (_loop_i + 1);
                  std::shared_ptr<list<unsigned int>> _next_l = _args.d_a1;
                  _loop_i = std::move(_next_i);
                  _loop_l = std::move(_next_l);
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<list<unsigned int>>
  find_indices(F0 &&p, const std::shared_ptr<list<unsigned int>> &l) {
    return find_indices_aux(p, l, 0u);
  }

  /// member x l checks if x is in the list.
  __attribute__((pure)) static bool
  member(const unsigned int x, const std::shared_ptr<list<unsigned int>> &l);
  /// product l multiplies all elements in the list.
  __attribute__((pure)) static unsigned int
  product(const std::shared_ptr<list<unsigned int>> &l);
  /// sum_list l sums all elements in the list.
  __attribute__((pure)) static unsigned int
  sum_list(const std::shared_ptr<list<unsigned int>> &l);

  /// flatten l flattens a list of lists.
  template <typename T1>
  static std::shared_ptr<list<T1>>
  flatten(const std::shared_ptr<list<std::shared_ptr<list<T1>>>> &l) {
    struct _Enter {
      const std::shared_ptr<list<std::shared_ptr<list<T1>>>> l;
    };

    struct _Call1 {
      decltype(std::declval<
                   const typename list<std::shared_ptr<list<T1>>>::Cons &>()
                   .d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<std::shared_ptr<list<T1>>>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<std::shared_ptr<list<T1>>>::Nil
                                &) -> void { _result = list<T1>::nil(); },
                        [&](const typename list<std::shared_ptr<list<T1>>>::Cons
                                &_args) -> void {
                          std::function<std::shared_ptr<list<T1>>(
                              std::shared_ptr<list<T1>>,
                              std::shared_ptr<list<T1>>)>
                              app;
                          app = [&](std::shared_ptr<list<T1>> l1,
                                    std::shared_ptr<list<T1>> l2)
                              -> std::shared_ptr<list<T1>> {
                            struct _Enter {
                              std::shared_ptr<list<T1>> l1;
                            };
                            struct _Call1 {
                              decltype(std::declval<
                                           const typename list<T1>::Cons &>()
                                           .d_a0) _s0;
                            };
                            using _Frame = std::variant<_Enter, _Call1>;
                            std::shared_ptr<list<T1>> _result{};
                            std::vector<_Frame> _stack;
                            _stack.emplace_back(_Enter{l1});
                            while (!_stack.empty()) {
                              _Frame _frame = std::move(_stack.back());
                              _stack.pop_back();
                              std::visit(
                                  Overloaded{
                                      [&](_Enter _f) {
                                        std::shared_ptr<list<T1>> l1 = _f.l1;
                                        std::visit(
                                            Overloaded{
                                                [&](const typename list<T1>::Nil
                                                        &) -> void {
                                                  _result = std::move(l2);
                                                },
                                                [&](const typename list<
                                                    T1>::Cons &_args0) -> void {
                                                  _stack.emplace_back(
                                                      _Call1{_args0.d_a0});
                                                  _stack.emplace_back(
                                                      _Enter{_args0.d_a1});
                                                }},
                                            l1->v());
                                      },
                                      [&](_Call1 _f) {
                                        _result =
                                            list<T1>::cons(_f._s0, _result);
                                      }},
                                  _frame);
                            }
                            return _result;
                          };
                          _stack.emplace_back(_Call1{_args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = app(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// flatten_nested l alternative flatten with different pattern: flattens one
  /// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
  /// :: flatten (xs :: rest).
  static std::shared_ptr<list<unsigned int>> flatten_nested_fuel(
      const unsigned int fuel,
      const std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>> &l);
  __attribute__((pure)) static unsigned int sum_list_lengths(
      const std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>> &l);
  static std::shared_ptr<list<unsigned int>> flatten_nested(
      const std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
          &l); /// compress l removes consecutive duplicates: 1,1,2,2,2,3 ->
               /// 1,2,3.
  static std::shared_ptr<list<unsigned int>>
  compress(const std::shared_ptr<list<unsigned int>> &l);
  /// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
  /// (1,2),(3,4).
  static std::shared_ptr<list<std::pair<unsigned int, unsigned int>>>
  group_pairs(const std::shared_ptr<list<unsigned int>> &l);
  /// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  swizzle(const std::shared_ptr<list<unsigned int>> &l);
  /// index_of_aux x l i finds first index of x in l starting from i.
  __attribute__((pure)) static unsigned int
  index_of_aux(const unsigned int x,
               const std::shared_ptr<list<unsigned int>> &l,
               const unsigned int i);
  __attribute__((pure)) static unsigned int
  index_of(const unsigned int x, const std::shared_ptr<list<unsigned int>> &l);
  /// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
  static std::shared_ptr<list<unsigned int>>
  interleave(std::shared_ptr<list<unsigned int>> l1,
             std::shared_ptr<list<unsigned int>> l2);
  /// lookup key l finds value for key in association list.
  __attribute__((pure)) static unsigned int
  lookup(const unsigned int key,
         const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);
  /// group l groups consecutive equal elements: 1,1,2,2,2,3 ->
  /// [1,1],[2,2,2],[3].
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  group_fuel(const unsigned int fuel,
             const std::shared_ptr<list<unsigned int>> &l);
  static std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>>
  group(const std::shared_ptr<list<unsigned int>> &l);
  /// Internal helper: reverse a list.
  static std::shared_ptr<list<unsigned int>>
  rev_helper(std::shared_ptr<list<unsigned int>> acc,
             const std::shared_ptr<list<unsigned int>> &l);
  /// reverse_insert x l inserts x and reverses at each step.
  static std::shared_ptr<list<unsigned int>>
  reverse_insert(const unsigned int x,
                 const std::shared_ptr<list<unsigned int>> &l);
  /// Internal helper: append lists.
  static std::shared_ptr<list<unsigned int>>
  app_helper(const std::shared_ptr<list<unsigned int>> &l1,
             std::shared_ptr<list<unsigned int>> l2);
  /// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
  static std::shared_ptr<list<unsigned int>>
  double_append(const std::shared_ptr<list<unsigned int>> &l1,
                std::shared_ptr<list<unsigned int>> l2);
  /// remove_if_sum_even l removes element if sum with next is even.
  static std::shared_ptr<list<unsigned int>>
  remove_if_sum_even(const std::shared_ptr<list<unsigned int>> &l);
  /// split_at n l splits list at index n into (prefix, suffix).
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  split_at(const unsigned int n, std::shared_ptr<list<unsigned int>> l);

  /// span p l splits list at first element not satisfying p.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  span(F0 &&p, std::shared_ptr<list<unsigned int>> l) {
    struct _Enter {
      std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {
      const typename list<unsigned int>::Cons _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<list<unsigned int>>,
              std::shared_ptr<list<unsigned int>>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil &) -> void {
                          _result = std::make_pair(list<unsigned int>::nil(),
                                                   list<unsigned int>::nil());
                        },
                        [&](const typename list<unsigned int>::Cons &_args)
                            -> void {
                          if (p(_args.d_a0)) {
                            _stack.emplace_back(_Call1{_args});
                            _stack.emplace_back(_Enter{_args.d_a1});
                          } else {
                            _result = std::make_pair(list<unsigned int>::nil(),
                                                     std::move(l));
                          }
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename list<unsigned int>::Cons _args = _f._s0;
                const std::shared_ptr<list<unsigned int>> &a = _result.first;
                const std::shared_ptr<list<unsigned int>> &b = _result.second;
                _result =
                    std::make_pair(list<unsigned int>::cons(_args.d_a0, a), b);
              }},
          _frame);
    }
    return _result;
  }

  /// unzip l splits list of pairs into two lists.
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  unzip(const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);
  /// nth n l default returns nth element or default if out of bounds.
  __attribute__((pure)) static unsigned int
  nth(const unsigned int n, const std::shared_ptr<list<unsigned int>> &l,
      const unsigned int default0);
  /// last l default returns last element or default if empty.
  __attribute__((pure)) static unsigned int
  last(const std::shared_ptr<list<unsigned int>> &l,
       const unsigned int default0);
  /// drop n l drops first n elements.
  static std::shared_ptr<list<unsigned int>>
  drop(const unsigned int n, std::shared_ptr<list<unsigned int>> l);
  /// init l returns all but last element.
  static std::shared_ptr<list<unsigned int>>
  init(const std::shared_ptr<list<unsigned int>> &l);
  /// count x l counts occurrences of x in l.
  __attribute__((pure)) static unsigned int
  count(const unsigned int x, const std::shared_ptr<list<unsigned int>> &l);
  /// maximum l finds maximum element (returns 0 for empty list).
  __attribute__((pure)) static unsigned int
  maximum(const std::shared_ptr<list<unsigned int>> &l);
  /// minmax l finds both minimum and maximum in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  minmax(const std::shared_ptr<list<unsigned int>> &l);
  /// Helper for rotate_left.
  static std::shared_ptr<list<unsigned int>>
  rotate_left_fuel(const unsigned int fuel, const unsigned int n,
                   std::shared_ptr<list<unsigned int>> l);
  /// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
  /// 3,4,1,2.
  static std::shared_ptr<list<unsigned int>>
  rotate_left(const unsigned int n,
              const std::shared_ptr<list<unsigned int>> &l);
  /// intercalate sep lists joins lists with separator: intercalate 0
  /// [1,2],[3,4] -> 1,2,0,3,4.
  static std::shared_ptr<list<unsigned int>> intercalate(
      const std::shared_ptr<list<unsigned int>> &sep,
      const std::shared_ptr<list<std::shared_ptr<list<unsigned int>>>> &lists);
  /// majority l finds majority element using Boyer-Moore voting algorithm.
  /// Returns (candidate, count).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  majority(const std::shared_ptr<list<unsigned int>> &l);
  /// zip3 l1 l2 l3 zips three lists into triples.
  static std::shared_ptr<
      list<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
  zip3(const std::shared_ptr<list<unsigned int>> &l1,
       const std::shared_ptr<list<unsigned int>> &l2,
       const std::shared_ptr<list<unsigned int>> &l3);
  /// sum_and_count l returns both sum and count in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  sum_and_count(const std::shared_ptr<list<unsigned int>> &l);
  /// elem_at n l returns element at index n (like nth but with different name).
  __attribute__((pure)) static std::optional<unsigned int>
  elem_at(const unsigned int n, const std::shared_ptr<list<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LISTS
