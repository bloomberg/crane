#ifndef INCLUDED_LOOPIFY_HOFS
#define INCLUDED_LOOPIFY_HOFS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

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
          Overloaded{
              [&](_Enter _f) {
                const List *_self = _f._self;
                std::visit(
                    Overloaded{
                        [&](const typename List<t_A>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1.get()});
                        }},
                    _self->v());
              },
              [&](_Call1) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_self = _args.d_a1.get();
              }},
          _loop_self->v());
    }
    return _head;
  }
};

struct LoopifyHofs {
  /// foldl1 f l folds from left with no initial value. Returns 0 for empty
  /// list.
  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 foldl1_aux(F0 &&f, const T1 acc,
                       const std::shared_ptr<List<T1>> &l) {
    T1 _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    T1 _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<T1>::Nil) {
                              _result = _loop_acc;
                              _continue = false;
                            },
                            [&](const typename List<T1>::Cons _args) {
                              std::shared_ptr<List<T1>> _next_l = _args.d_a1;
                              T1 _next_acc = f(_loop_acc, _args.d_a0);
                              _loop_l = std::move(_next_l);
                              _loop_acc = std::move(_next_acc);
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 foldl1(F0 &&f, const T1 default0,
                   const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename List<T1>::Nil) -> T1 { return default0; },
                   [&](const typename List<T1>::Cons _args) -> T1 {
                     return foldl1_aux<T1>(f, _args.d_a0, _args.d_a1);
                   }},
        l->v());
  }

  /// forall_ p l checks if all elements satisfy predicate p.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static bool
  forall_(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    bool _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<T1>::Nil) {
                              _result = true;
                              _continue = false;
                            },
                            [&](const typename List<T1>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _loop_l = _args.d_a1;
                              } else {
                                _result = false;
                                _continue = false;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// exists_fn p l checks if any element satisfies predicate p.
  template <typename T1, MapsTo<bool, T1> F0>
  __attribute__((pure)) static bool
  exists_fn(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    bool _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<T1>::Nil) {
                              _result = false;
                              _continue = false;
                            },
                            [&](const typename List<T1>::Cons _args) {
                              if (p(_args.d_a0)) {
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

  /// drop_while p l drops elements while predicate holds.
  template <typename T1, MapsTo<bool, T1> F0>
  static std::shared_ptr<List<T1>>
  drop_while(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    std::shared_ptr<List<T1>> _result;
    std::shared_ptr<List<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<T1>::Nil) {
                              _result = List<T1>::nil();
                              _continue = false;
                            },
                            [&](const typename List<T1>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _loop_l = _args.d_a1;
                              } else {
                                _result =
                                    List<T1>::cons(_args.d_a0, _args.d_a1);
                                _continue = false;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// take_while p l takes elements while predicate holds.
  template <typename T1, MapsTo<bool, T1> F0>
  static std::shared_ptr<List<T1>>
  take_while(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> _last{};
    std::shared_ptr<List<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<T1>::Nil) {
                if (_last) {
                  std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
                      List<T1>::nil();
                } else {
                  _head = List<T1>::nil();
                }
                _continue = false;
              },
              [&](const typename List<T1>::Cons _args) {
                if (p(_args.d_a0)) {
                  auto _cell = List<T1>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
                        _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                } else {
                  if (_last) {
                    std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
                        List<T1>::nil();
                  } else {
                    _head = List<T1>::nil();
                  }
                  _continue = false;
                }
              }},
          _loop_l->v());
    }
    return _head;
  } /// flat_map f l maps f and flattens results.

  template <typename T1, typename T2, MapsTo<std::shared_ptr<List<T2>>, T1> F0>
  static std::shared_ptr<List<T2>>
  flat_map(F0 &&f, const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      std::shared_ptr<List<T2>> _s0;
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
                        [&](const typename List<T1>::Nil) -> void {
                          _result = List<T2>::nil();
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{f(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = _f._s0->app(_result); }},
          _frame);
    }
    return _result;
  }

  /// all_pairs l1 l2 returns all pairs from two lists.
  template <typename T1, typename T2>
  static std::shared_ptr<List<std::pair<T1, T2>>>
  all_pairs(const std::shared_ptr<List<T1>> &l1,
            const std::shared_ptr<List<T2>> &l2) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l1;
    };

    struct _Call1 {
      std::shared_ptr<List<std::pair<T1, T2>>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<std::pair<T1, T2>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l1 = _f.l1;
                std::function<std::shared_ptr<List<std::pair<T1, T2>>>(
                    T1, std::shared_ptr<List<T2>>)>
                    pair_with;
                pair_with = [&](T1 x, std::shared_ptr<List<T2>> l)
                    -> std::shared_ptr<List<std::pair<T1, T2>>> {
                  struct _Enter {
                    std::shared_ptr<List<T2>> l;
                  };
                  struct _Call1 {
                    decltype(std::make_pair(
                        std::declval<T1 &>(),
                        std::declval<const typename List<T2>::Cons &>()
                            .d_a0)) _s0;
                  };
                  using _Frame = std::variant<_Enter, _Call1>;
                  std::shared_ptr<List<std::pair<T1, T2>>> _result{};
                  std::vector<_Frame> _stack;
                  _stack.push_back(_Enter{l});
                  while (!_stack.empty()) {
                    _Frame _frame = std::move(_stack.back());
                    _stack.pop_back();
                    std::visit(
                        Overloaded{
                            [&](_Enter _f) {
                              std::shared_ptr<List<T2>> l = _f.l;
                              std::visit(
                                  Overloaded{
                                      [&](const typename List<T2>::Nil)
                                          -> void {
                                        _result =
                                            List<std::pair<T1, T2>>::nil();
                                      },
                                      [&](const typename List<T2>::Cons _args)
                                          -> void {
                                        _stack.push_back(_Call1{
                                            std::make_pair(x, _args.d_a0)});
                                        _stack.push_back(_Enter{_args.d_a1});
                                      }},
                                  l->v());
                            },
                            [&](_Call1 _f) {
                              _result = List<std::pair<T1, T2>>::cons(_f._s0,
                                                                      _result);
                            }},
                        _frame);
                  }
                  return _result;
                };
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil) -> void {
                          _result = List<std::pair<T1, T2>>::nil();
                        },
                        [&](const typename List<T1>::Cons _args0) -> void {
                          _stack.push_back(_Call1{pair_with(_args0.d_a0, l2)});
                          _stack.push_back(_Enter{_args0.d_a1});
                        }},
                    l1->v());
              },
              [&](_Call1 _f) { _result = _f._s0->app(_result); }},
          _frame);
    }
    return _result;
  }

  /// find_indices p l finds all indices where p is true.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices_aux(F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
                   const unsigned int i) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_i = i;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (p(_args.d_a0)) {
                  auto _cell = List<unsigned int>::cons(_loop_i, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  unsigned int _next_i = (_loop_i + 1);
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_i = std::move(_next_i);
                  _loop_l = std::move(_next_l);
                } else {
                  unsigned int _next_i = (_loop_i + 1);
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_i = std::move(_next_i);
                  _loop_l = std::move(_next_l);
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_indices_aux(p, l, 0u);
  }

  /// delete_by eq x l deletes first element equal to x.
  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  delete_by(F0 &&eq, const unsigned int x,
            const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (eq(x, _args.d_a0)) {
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _args.d_a1;
                  } else {
                    _head = _args.d_a1;
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
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  __attribute__((pure)) static bool
  is_prefix_of(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  /// lookup_all key l finds all values associated with key in association list.
  static std::shared_ptr<List<unsigned int>> lookup_all(
      const unsigned int key,
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);

  /// scanl f acc l scan from left with accumulator.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanl(F0 &&f, const unsigned int acc,
        const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(
                      _loop_acc, List<unsigned int>::nil());
                } else {
                  _head = List<unsigned int>::cons(_loop_acc,
                                                   List<unsigned int>::nil());
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_acc = f(_loop_acc, _args.d_a0);
                _loop_l = std::move(_next_l);
                _loop_acc = std::move(_next_acc);
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// scanl1 f l like scanl but no initial value, uses first element.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  scanl1_fuel(const unsigned int fuel, F1 &&f,
              std::shared_ptr<List<unsigned int>> l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                std::move(_loop_l);
          } else {
            _head = std::move(_loop_l);
          }
          _continue = false;
        }
      } else {
        unsigned int g = _loop_fuel - 1;
        if (_loop_l.use_count() == 1 && _loop_l->v().index() == 0) {
          auto &_rf = std::get<0>(_loop_l->v_mut());
          {
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _loop_l;
            } else {
              _head = _loop_l;
            }
            _continue = false;
          }
        } else {
          std::visit(
              Overloaded{
                  [&](const typename List<unsigned int>::Nil) {
                    if (_last) {
                      std::get<typename List<unsigned int>::Cons>(
                          _last->v_mut())
                          .d_a1 = List<unsigned int>::nil();
                    } else {
                      _head = List<unsigned int>::nil();
                    }
                    _continue = false;
                  },
                  [&](const typename List<unsigned int>::Cons _args) {
                    std::visit(
                        Overloaded{
                            [&](const typename List<unsigned int>::Nil) {
                              if (_last) {
                                std::get<typename List<unsigned int>::Cons>(
                                    _last->v_mut())
                                    .d_a1 = List<unsigned int>::cons(
                                    _args.d_a0, List<unsigned int>::nil());
                              } else {
                                _head = List<unsigned int>::cons(
                                    _args.d_a0, List<unsigned int>::nil());
                              }
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons
                                    _args0) {
                              auto _cell =
                                  List<unsigned int>::cons(_args.d_a0, nullptr);
                              if (_last) {
                                std::get<typename List<unsigned int>::Cons>(
                                    _last->v_mut())
                                    .d_a1 = _cell;
                              } else {
                                _head = _cell;
                              }
                              _last = _cell;
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  List<unsigned int>::cons(
                                      f(_args.d_a0, _args0.d_a0), _args0.d_a1);
                              unsigned int _next_fuel = g;
                              _loop_l = std::move(_next_l);
                              _loop_fuel = std::move(_next_fuel);
                            }},
                        _args.d_a1->v());
                  }},
              _loop_l->v());
        }
      }
    }
    return _head;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanl1(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    return scanl1_fuel(l->length(), f, l);
  }

  /// foldr1 f l fold right with no initial value.
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil)
                                      -> void { _result = _args.d_a0; },
                                  [&](const typename List<unsigned int>::Cons)
                                      -> void {
                                    _stack.push_back(_Call1{_args.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// Helper: get head of list with default.
  __attribute__((pure)) static unsigned int
  head_default(const unsigned int default0,
               const std::shared_ptr<List<unsigned int>> &l);

  /// scanr f acc l scan from right.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanr(F0 &&f, const unsigned int acc,
        const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      const unsigned int _s1;
      F0 _s2;
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = List<unsigned int>::cons(
                              acc, List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args, acc, f});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                const unsigned int acc = _f._s1;
                F0 f = _f._s2;
                std::shared_ptr<List<unsigned int>> rest = _result;
                unsigned int h = head_default(acc, rest);
                _result = List<unsigned int>::cons(f(_args.d_a0, h), rest);
              }},
          _frame);
    }
    return _result;
  }

  /// scanr1 f l scanr with no initial value.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanr1(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = List<unsigned int>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil)
                                      -> void {
                                    _result = List<unsigned int>::cons(
                                        _args.d_a0, List<unsigned int>::nil());
                                  },
                                  [&](const typename List<unsigned int>::Cons)
                                      -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                std::shared_ptr<List<unsigned int>> rest = _result;
                unsigned int h = head_default(_args.d_a0, rest);
                _result = List<unsigned int>::cons(f(_args.d_a0, h), rest);
              }},
          _frame);
    }
    return _result;
  }

  /// mapcat f l maps f and concatenates results (concat_map).
  template <typename T1, MapsTo<std::shared_ptr<List<T1>>, unsigned int> F0>
  static std::shared_ptr<List<T1>>
  mapcat(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      std::shared_ptr<List<T1>> _s0;
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
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = List<T1>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{f(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = _f._s0->app(_result); }},
          _frame);
    }
    return _result;
  }

  /// map_maybe f l maps f and filters out None results.
  template <MapsTo<std::optional<unsigned int>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  map_maybe(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = List<unsigned int>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args, f});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                std::shared_ptr<List<unsigned int>> rest = _result;
                if (f(_args.d_a0).has_value()) {
                  unsigned int y = *f(_args.d_a0);
                  _result = List<unsigned int>::cons(y, rest);
                } else {
                  _result = std::move(rest);
                }
              }},
          _frame);
    }
    return _result;
  }

  /// bool_all p l checks if all elements satisfy p (same as forall_).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  bool_all(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = true;
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{p(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = (_f._s0 && _result); }},
          _frame);
    }
    return _result;
  }

  /// merge_by cmp l1 l2 merges two lists using comparison function.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  merge_by_fuel(const unsigned int fuel, F1 &&cmp,
                std::shared_ptr<List<unsigned int>> l1,
                std::shared_ptr<List<unsigned int>> l2) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
    std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                std::move(_loop_l1);
          } else {
            _head = std::move(_loop_l1);
          }
          _continue = false;
        }
      } else {
        unsigned int f = _loop_fuel - 1;
        std::visit(
            Overloaded{
                [&](const typename List<unsigned int>::Nil) {
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = std::move(_loop_l2);
                  } else {
                    _head = std::move(_loop_l2);
                  }
                  _continue = false;
                },
                [&](const typename List<unsigned int>::Cons _args) {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil) {
                            if (_last) {
                              std::get<typename List<unsigned int>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = std::move(_loop_l1);
                            } else {
                              _head = std::move(_loop_l1);
                            }
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args0) {
                            if (cmp(_args.d_a0, _args0.d_a0) <= 0u) {
                              auto _cell =
                                  List<unsigned int>::cons(_args.d_a0, nullptr);
                              if (_last) {
                                std::get<typename List<unsigned int>::Cons>(
                                    _last->v_mut())
                                    .d_a1 = _cell;
                              } else {
                                _head = _cell;
                              }
                              _last = _cell;
                              std::shared_ptr<List<unsigned int>> _next_l1 =
                                  _args.d_a1;
                              unsigned int _next_fuel = f;
                              _loop_l1 = std::move(_next_l1);
                              _loop_fuel = std::move(_next_fuel);
                            } else {
                              auto _cell = List<unsigned int>::cons(_args0.d_a0,
                                                                    nullptr);
                              if (_last) {
                                std::get<typename List<unsigned int>::Cons>(
                                    _last->v_mut())
                                    .d_a1 = _cell;
                              } else {
                                _head = _cell;
                              }
                              _last = _cell;
                              std::shared_ptr<List<unsigned int>> _next_l2 =
                                  _args0.d_a1;
                              unsigned int _next_fuel = f;
                              _loop_l2 = std::move(_next_l2);
                              _loop_fuel = std::move(_next_fuel);
                            }
                          }},
                      _loop_l2->v());
                }},
            _loop_l1->v());
      }
    }
    return _head;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  merge_by(F0 &&cmp, const std::shared_ptr<List<unsigned int>> &l1,
           const std::shared_ptr<List<unsigned int>> &l2) {
    return merge_by_fuel((l1->length() + l2->length()), cmp, l1, l2);
  }

  /// max_by f l finds element with maximum f value.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  max_by(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil)
                                      -> void { _result = f(_args.d_a0); },
                                  [&](const typename List<unsigned int>::Cons)
                                      -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                unsigned int rest_max = _result;
                unsigned int fx = f(_args.d_a0);
                if (rest_max <= fx) {
                  _result = fx;
                } else {
                  _result = rest_max;
                }
              }},
          _frame);
    }
    return _result;
  }

  /// iterate f n x generates x, f(x), f(f(x)), ... of length n.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  iterate(F0 &&f, const unsigned int n, const unsigned int x) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_x = x;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int m = _loop_n - 1;
        {
          auto _cell = List<unsigned int>::cons(_loop_x, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          unsigned int _next_x = f(_loop_x);
          unsigned int _next_n = m;
          _loop_x = std::move(_next_x);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _head;
  }

  /// maximum_by cmp l finds maximum element by comparison function.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  maximum_by(F0 &&cmp, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil)
                                      -> void { _result = _args.d_a0; },
                                  [&](const typename List<unsigned int>::Cons)
                                      -> void {
                                    _stack.push_back(_Call1{_args, cmp});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 cmp = _f._s1;
                unsigned int m = _result;
                if (0u <= cmp(_args.d_a0, m)) {
                  _result = _args.d_a0;
                } else {
                  _result = m;
                }
              }},
          _frame);
    }
    return _result;
  }

  /// fold_right f l acc folds from the right.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_right(F0 &&f, const std::shared_ptr<List<unsigned int>> &l,
             const unsigned int acc) {
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = acc;
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// partition p l partitions list into (satisfies p, doesn't satisfy p).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  partition(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      F0 _s0;
      const typename List<unsigned int>::Cons _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<unsigned int>>,
              std::shared_ptr<List<unsigned int>>>
        _result{};
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = std::make_pair(List<unsigned int>::nil(),
                                                   List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{p, _args});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                F0 p = _f._s0;
                const typename List<unsigned int>::Cons _args = _f._s1;
                std::shared_ptr<List<unsigned int>> yes = _result.first;
                std::shared_ptr<List<unsigned int>> no = _result.second;
                if (p(_args.d_a0)) {
                  _result = std::make_pair(
                      List<unsigned int>::cons(_args.d_a0, yes), no);
                } else {
                  _result = std::make_pair(
                      yes, List<unsigned int>::cons(_args.d_a0, no));
                }
              }},
          _frame);
    }
    return _result;
  }

  /// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  subsequences(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: pair element with all elements in list.
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  pair_with_all(const unsigned int x,
                const std::shared_ptr<List<unsigned int>> &l);
  /// cartesian l1 l2 computes cartesian product of two lists.
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  cartesian(const std::shared_ptr<List<unsigned int>> &l1,
            const std::shared_ptr<List<unsigned int>> &l2);
  /// longest_run l finds the longest consecutive run of equal elements.
  /// Matches on recursive result to decide behavior.
  static std::shared_ptr<List<unsigned int>>
  longest_run_fuel(const unsigned int fuel,
                   std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  longest_run(const std::shared_ptr<List<unsigned int>> &l);

  /// any p l checks if any element satisfies predicate (same as exists_fn but
  /// different name).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  any(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    bool _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil) {
                              _result = false;
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
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

  /// all p l checks if all elements satisfy predicate (same as forall_ but
  /// different name).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  all(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    bool _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil) {
                              _result = true;
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _loop_l = _args.d_a1;
                              } else {
                                _result = false;
                                _continue = false;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// filter_not p l filters elements that don't satisfy predicate.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  filter_not(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (p(_args.d_a0)) {
                  _loop_l = _args.d_a1;
                } else {
                  auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
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

  /// span_split p l splits at first element that doesn't satisfy p.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  span_split(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<unsigned int>>,
              std::shared_ptr<List<unsigned int>>>
        _result{};
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = std::make_pair(List<unsigned int>::nil(),
                                                   List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _result =
                                std::make_pair(List<unsigned int>::nil(),
                                               List<unsigned int>::cons(
                                                   _args.d_a0, _args.d_a1));
                          }
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                std::shared_ptr<List<unsigned int>> taken = _result.first;
                std::shared_ptr<List<unsigned int>> rest = _result.second;
                _result = std::make_pair(
                    List<unsigned int>::cons(_args.d_a0, taken), rest);
              }},
          _frame);
    }
    return _result;
  }

  /// group_by_eq eq l groups consecutive elements by equality function.
  template <MapsTo<bool, unsigned int, unsigned int> F1>
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  group_by_eq_fuel(const unsigned int fuel, F1 &&eq,
                   const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
      const unsigned int fuel;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
    };

    struct _Call2 {
      decltype(List<unsigned int>::cons(
          std::declval<const typename List<unsigned int>::Cons &>().d_a0,
          List<unsigned int>::nil())) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                const unsigned int fuel = _f.fuel;
                if (fuel <= 0) {
                  _result = List<std::shared_ptr<List<unsigned int>>>::nil();
                } else {
                  unsigned int f = fuel - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil) -> void {
                            _result = List<
                                std::shared_ptr<List<unsigned int>>>::nil();
                          },
                          [&](const typename List<unsigned int>::Cons _args)
                              -> void {
                            std::visit(
                                Overloaded{
                                    [&](const typename List<unsigned int>::Nil)
                                        -> void {
                                      _result = List<
                                          std::shared_ptr<List<unsigned int>>>::
                                          cons(List<unsigned int>::cons(
                                                   _args.d_a0,
                                                   List<unsigned int>::nil()),
                                               List<std::shared_ptr<
                                                   List<unsigned int>>>::nil());
                                    },
                                    [&](const typename List<unsigned int>::Cons
                                            _args0) -> void {
                                      if (eq(_args.d_a0, _args0.d_a0)) {
                                        _stack.push_back(_Call1{_args});
                                        _stack.push_back(_Enter{_args.d_a1, f});
                                      } else {
                                        _stack.push_back(
                                            _Call2{List<unsigned int>::cons(
                                                _args.d_a0,
                                                List<unsigned int>::nil())});
                                        _stack.push_back(_Enter{_args.d_a1, f});
                                      }
                                    }},
                                _args.d_a1->v());
                          }},
                      l->v());
                }
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<List<unsigned int>>>::Nil) -> void {
                          _result =
                              List<std::shared_ptr<List<unsigned int>>>::cons(
                                  List<unsigned int>::cons(
                                      _args.d_a0, List<unsigned int>::nil()),
                                  List<std::shared_ptr<List<unsigned int>>>::
                                      nil());
                        },
                        [&](const typename List<
                            std::shared_ptr<List<unsigned int>>>::Cons _args1)
                            -> void {
                          _result =
                              List<std::shared_ptr<List<unsigned int>>>::cons(
                                  List<unsigned int>::cons(_args.d_a0,
                                                           _args1.d_a0),
                                  _args1.d_a1);
                        }},
                    _result->v());
              },
              [&](_Call2 _f) {
                _result = List<std::shared_ptr<List<unsigned int>>>::cons(
                    _f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  group_by_eq(F0 &&eq, const std::shared_ptr<List<unsigned int>> &l) {
    return group_by_eq_fuel(l->length(), eq, l);
  }

  /// power_set l generates all subsets.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  power_set(const std::shared_ptr<List<unsigned int>> &l);

  /// map_accum_l f acc l maps with accumulator threading.
  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((
      pure)) static std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>
  map_accum_l(F0 &&f, const unsigned int acc,
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result =
                              std::make_pair(acc, List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          unsigned int acc_ = f(acc, _args.d_a0).first;
                          unsigned int y = f(acc, _args.d_a0).second;
                          _stack.push_back(_Call1{y});
                          _stack.push_back(_Enter{_args.d_a1, acc_});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                unsigned int y = _f._s0;
                unsigned int acc__ = _result.first;
                std::shared_ptr<List<unsigned int>> ys = _result.second;
                _result =
                    std::make_pair(acc__, List<unsigned int>::cons(y, ys));
              }},
          _frame);
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_HOFS
