#ifndef INCLUDED_LOOPIFY_TMC
#define INCLUDED_LOOPIFY_TMC

#include <memory>
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

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
struct LoopifyTmc {
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

  /// app l1 l2 appends two lists. Basic TMC pattern: cons head (app tail l2).
  template <typename T1>
  static std::shared_ptr<list<T1>> app(const std::shared_ptr<list<T1>> &l1,
                                       std::shared_ptr<list<T1>> l2) {
    std::shared_ptr<list<T1>> _head{};
    std::shared_ptr<list<T1>> _last{};
    std::shared_ptr<list<T1>> _loop_l1 = l1;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                      std::move(l2);
                } else {
                  _head = std::move(l2);
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
                _loop_l1 = _args.d_a1;
              }},
          _loop_l1->v());
    }
    return _head;
  }

  /// map f l applies f to every element. TMC with element transform.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<list<T2>> map(F0 &&f,
                                       const std::shared_ptr<list<T1>> &l) {
    std::shared_ptr<list<T2>> _head{};
    std::shared_ptr<list<T2>> _last{};
    std::shared_ptr<list<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename list<T1>::Nil &) {
                if (_last) {
                  std::get<typename list<T2>::Cons>(_last->v_mut()).d_a1 =
                      list<T2>::nil();
                } else {
                  _head = list<T2>::nil();
                }
                _continue = false;
              },
              [&](const typename list<T1>::Cons &_args) {
                auto _cell = list<T2>::cons(f(_args.d_a0), nullptr);
                if (_last) {
                  std::get<typename list<T2>::Cons>(_last->v_mut()).d_a1 =
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

  /// filter f l keeps elements satisfying f. Mixed tail + TMC branches.
  template <typename T1, MapsTo<bool, T1> F0>
  static std::shared_ptr<list<T1>> filter(F0 &&f,
                                          const std::shared_ptr<list<T1>> &l) {
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
                if (f(_args.d_a0)) {
                  auto _cell = list<T1>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename list<T1>::Cons>(_last->v_mut()).d_a1 =
                        _cell;
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

  /// snoc l x appends x at the end. TMC, base case allocates a cell.
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

  /// replicate n x creates n copies of x. Nat recursion producing list.
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

  /// range lo hi creates lo, lo+1, ..., hi-1.
  static std::shared_ptr<list<unsigned int>> range(const unsigned int lo,
                                                   const unsigned int hi);

  /// zip_with f l1 l2 combines two lists element-wise. Two varying params.
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

  /// prefix_sums acc l computes running prefix sums.
  static std::shared_ptr<list<unsigned int>>
  prefix_sums(const unsigned int acc,
              const std::shared_ptr<list<unsigned int>> &l);

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2. Nested TMC.
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
};

#endif // INCLUDED_LOOPIFY_TMC
