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
concept MapsTo = std::is_invocable_v<F &, Args &...>;

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
struct LoopifyLists {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(
            Cons{d_a0,
                 d_a1 ? std::make_unique<LoopifyLists::list<t_A>>(d_a1->clone())
                      : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2.
  template <typename T1>
  __attribute__((pure)) static list<T1> stutter(const list<T1> &l) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        auto _cell1 =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        std::get<typename list<T1>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>(
                      std::get<typename list<T1>::Cons>((*_write)->v_mut())
                          .d_a1->v_mut())
                      .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// snoc l x appends x at the end (reverse cons).
  template <typename T1>
  __attribute__((pure)) static list<T1> snoc(const list<T1> &l, const T1 x) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) =
            std::make_unique<list<T1>>(list<T1>::cons(x, list<T1>::nil()));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// intersperse sep l inserts separator between elements.
  template <typename T1>
  __attribute__((pure)) static list<T1> intersperse(const T1 sep,
                                                    const list<T1> &l) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
          *(_write) =
              std::make_unique<list<T1>>(list<T1>::cons(d_a0, list<T1>::nil()));
          break;
        } else {
          auto _cell = std::make_unique<list<T1>>(
              typename list<T1>::Cons(d_a0, nullptr));
          auto _cell1 =
              std::make_unique<list<T1>>(typename list<T1>::Cons(sep, nullptr));
          std::get<typename list<T1>::Cons>(_cell->v_mut()).d_a1 =
              std::move(_cell1);
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<T1>::Cons>(
                        std::get<typename list<T1>::Cons>((*_write)->v_mut())
                            .d_a1->v_mut())
                        .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// replicate n x creates n copies of x.
  template <typename T1>
  __attribute__((pure)) static list<T1> replicate(const unsigned int &n,
                                                  const T1 x) {
    std::unique_ptr<list<T1>> _head{};
    std::unique_ptr<list<T1>> *_write = &_head;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) = std::make_unique<list<T1>>(list<T1>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell =
            std::make_unique<list<T1>>(typename list<T1>::Cons(x, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T1>::Cons>((*_write)->v_mut()).d_a1;
        _loop_n = m;
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// replicate_list n l repeats list l n times.
  template <typename T1>
  __attribute__((pure)) static list<T1> replicate_list(const unsigned int &n,
                                                       const list<T1> &l) {
    struct _Enter {
      const unsigned int n;
    };

    struct _Call1 {
      const list<T1> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const unsigned int n = _f.n;
        std::function<list<T1>(list<T1>, list<T1>)> app;
        app = [&](list<T1> l1, list<T1> l2) -> list<T1> {
          struct _Enter {
            list<T1> l1;
          };
          struct _Call1 {
            T1 _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          list<T1> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{l1});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              list<T1> l1 = _f.l1;
              if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
                _result = l2;
              } else {
                const auto &[d_a0, d_a1] =
                    std::get<typename list<T1>::Cons>(l1.v());
                _stack.emplace_back(_Call1{d_a0});
                _stack.emplace_back(_Enter{*(d_a1)});
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = list<T1>::cons(_f._s0, _result);
            }
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
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = app(_f._s0, _result);
      }
    }
    return _result;
  }

  /// init_list n f generates f 0, f 1, ..., f (n-1).
  template <typename T1, MapsTo<T1, unsigned int> F1>
  __attribute__((pure)) static list<T1> init_list(unsigned int n, F1 &&f) {
    std::function<list<T1>(unsigned int)> go;
    go = [&](unsigned int i) -> list<T1> {
      struct _Enter {
        unsigned int i;
      };
      struct _Call1 {
        decltype(f((((n - std::declval<unsigned int &>()) > n
                         ? 0
                         : (n - std::declval<unsigned int &>()))))) _s0;
      };
      using _Frame = std::variant<_Enter, _Call1>;
      list<T1> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{i});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          unsigned int i = _f.i;
          if (i <= 0) {
            _result = list<T1>::nil();
          } else {
            unsigned int j = i - 1;
            _stack.emplace_back(_Call1{f((((n - i) > n ? 0 : (n - i))))});
            _stack.emplace_back(_Enter{j});
          }
        } else {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = list<T1>::cons(_f._s0, _result);
        }
      }
      return _result;
    };
    return go(n);
  }

  /// range start count generates start, start+1, ..., start+count-1.
  __attribute__((pure)) static list<unsigned int>
  range(unsigned int start, const unsigned int &count0);

  /// tails l returns all suffixes.
  template <typename T1>
  __attribute__((pure)) static list<list<T1>> tails(list<T1> l) {
    std::unique_ptr<list<list<T1>>> _head{};
    std::unique_ptr<list<list<T1>>> *_write = &_head;
    list<T1> _loop_l = std::move(l);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<list<T1>>>(
            list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil()));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<list<list<T1>>>(
            typename list<list<T1>>::Cons(_loop_l, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut()).d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// inits l returns all prefixes (complex recursion pattern).
  template <typename T1>
  __attribute__((pure)) static list<list<T1>> inits(const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      decltype(list<T1>::nil()) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result =
              list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          list<T1> d_a1_value = *(d_a1);
          std::function<list<list<T1>>(list<list<T1>>)> map_cons;
          map_cons = [&](list<list<T1>> ys) -> list<list<T1>> {
            struct _Enter {
              list<list<T1>> ys;
            };
            struct _Call1 {
              decltype(list<T1>::cons(std::declval<list<T1> &>(),
                                      std::declval<list<T1> &>())) _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            list<list<T1>> _result{};
            std::vector<_Frame> _stack;
            _stack.reserve(16);
            _stack.emplace_back(_Enter{ys});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                auto _f = std::move(std::get<_Enter>(_frame));
                list<list<T1>> ys = _f.ys;
                if (std::holds_alternative<typename list<list<T1>>::Nil>(
                        ys.v())) {
                  _result = list<list<T1>>::nil();
                } else {
                  const auto &[d_a0, d_a1] =
                      std::get<typename list<list<T1>>::Cons>(ys.v());
                  _stack.emplace_back(_Call1{list<T1>::cons(d_a0, d_a0)});
                  _stack.emplace_back(_Enter{*(d_a1)});
                }
              } else {
                auto _f = std::move(std::get<_Call1>(_frame));
                _result = list<list<T1>>::cons(_f._s0, _result);
              }
            }
            return _result;
          };
          _stack.emplace_back(_Call1{list<T1>::nil()});
          _stack.emplace_back(_Enter{d_a1_value});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = list<list<T1>>::cons(_f._s0, map_cons(_result));
      }
    }
    return _result;
  }

  /// scanl f acc l returns intermediate fold results.
  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  __attribute__((pure)) static list<T2> scanl(F0 &&f, const T2 acc,
                                              const list<T1> &l) {
    std::unique_ptr<list<T2>> _head{};
    std::unique_ptr<list<T2>> *_write = &_head;
    list<T1> _loop_l = l;
    T2 _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<T2>>(
            list<T2>::cons(_loop_acc, list<T2>::nil()));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        T2 new_acc = f(_loop_acc, d_a0);
        auto _cell = std::make_unique<list<T2>>(
            typename list<T2>::Cons(_loop_acc, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename list<T2>::Cons>((*_write)->v_mut()).d_a1;
        list<T1> _next_l = *(d_a1);
        T2 _next_acc = new_acc;
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// group_by eq l groups consecutive equal elements.
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static list<list<T1>>
  group_by_aux(F0 &&eq, const T1 prev, list<T1> acc, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<list<T1>>::cons(acc, list<list<T1>>::nil());
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      if (eq(prev, d_a0)) {
        return group_by_aux<T1>(eq, d_a0, list<T1>::cons(d_a0, acc), *(d_a1));
      } else {
        return list<list<T1>>::cons(
            acc, group_by_aux<T1>(
                     eq, d_a0, list<T1>::cons(d_a0, list<T1>::nil()), *(d_a1)));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static list<list<T1>> group_by(F0 &&eq,
                                                       const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<list<T1>>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return group_by_aux<T1>(eq, d_a0, list<T1>::cons(d_a0, list<T1>::nil()),
                              *(d_a1));
    }
  } /// chunks_of n l splits into chunks of size n.

  template <typename T1>
  __attribute__((pure)) static list<list<T1>>
  chunks_of_aux(const unsigned int &n, const list<T1> &l,
                const unsigned int &fuel) {
    std::unique_ptr<list<list<T1>>> _head{};
    std::unique_ptr<list<list<T1>>> *_write = &_head;
    unsigned int _loop_fuel = fuel;
    list<T1> _loop_l = l;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        std::function<list<T1>(unsigned int, list<T1>)> take;
        take = [&](unsigned int k, list<T1> lst) -> list<T1> {
          struct _Enter {
            list<T1> lst;
            unsigned int k;
          };
          struct _Call1 {
            T1 _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          list<T1> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{lst, k});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              list<T1> lst = _f.lst;
              unsigned int k = _f.k;
              if (k <= 0) {
                _result = list<T1>::nil();
              } else {
                unsigned int m = k - 1;
                if (std::holds_alternative<typename list<T1>::Nil>(lst.v())) {
                  _result = list<T1>::nil();
                } else {
                  const auto &[d_a0, d_a1] =
                      std::get<typename list<T1>::Cons>(lst.v());
                  _stack.emplace_back(_Call1{d_a0});
                  _stack.emplace_back(_Enter{*(d_a1), m});
                }
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = list<T1>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        std::function<list<T1>(unsigned int, list<T1>)> drop0;
        drop0 = [](unsigned int k, list<T1> lst) -> list<T1> {
          list<T1> _result;
          list<T1> _loop_lst = std::move(lst);
          unsigned int _loop_k = std::move(k);
          while (true) {
            if (_loop_k <= 0) {
              _result = _loop_lst;
              break;
            } else {
              unsigned int m = _loop_k - 1;
              if (std::holds_alternative<typename list<T1>::Nil>(
                      _loop_lst.v())) {
                _result = list<T1>::nil();
                break;
              } else {
                const auto &[d_a00, d_a10] =
                    std::get<typename list<T1>::Cons>(_loop_lst.v());
                list<T1> _next_lst = *(d_a10);
                unsigned int _next_k = m;
                _loop_lst = std::move(_next_lst);
                _loop_k = std::move(_next_k);
              }
            }
          }
          return _result;
        };
        if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
          *(_write) = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
          break;
        } else {
          list<T1> chunk = take(n, _loop_l);
          list<T1> rest = drop0(n, _loop_l);
          if (std::holds_alternative<typename list<T1>::Nil>(chunk.v())) {
            *(_write) = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
            break;
          } else {
            auto _cell = std::make_unique<list<list<T1>>>(
                typename list<list<T1>>::Cons(chunk, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut())
                     .d_a1;
            unsigned int _next_fuel = f;
            list<T1> _next_l = rest;
            _loop_fuel = std::move(_next_fuel);
            _loop_l = std::move(_next_l);
            continue;
          }
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  __attribute__((pure)) static list<list<T1>> chunks_of(const unsigned int &n,
                                                        const list<T1> &l) {
    std::function<unsigned int(list<T1>)> length;
    length = [&](list<T1> l0) -> unsigned int {
      struct _Enter {
        list<T1> l0;
      };
      struct _Call1 {};
      using _Frame = std::variant<_Enter, _Call1>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{l0});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          list<T1> l0 = _f.l0;
          if (std::holds_alternative<typename list<T1>::Nil>(l0.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename list<T1>::Cons>(l0.v());
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        } else {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = (_result + 1);
        }
      }
      return _result;
    };
    return chunks_of_aux<T1>(n, l, (length(l) + 1));
  }

  /// step_sum l sums with conditional contributions: even values as-is, odd
  /// doubled.
  __attribute__((pure)) static unsigned int
  step_sum(const list<unsigned int> &l);
  /// sum_abs l sums absolute values (using monus for nat).
  __attribute__((pure)) static unsigned int sum_abs(const list<unsigned int> &l,
                                                    const unsigned int &base);
  /// four_elem l multi-case pattern matching on list structure.
  __attribute__((pure)) static unsigned int
  four_elem(const list<unsigned int> &l);
  /// between lo hi l filters elements in range lo, hi.
  __attribute__((pure)) static list<unsigned int>
  between(const unsigned int &lo, const unsigned int &hi,
          const list<unsigned int> &l);

  /// count_matching p l counts elements satisfying predicate.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  count_matching(F0 &&p, const list<unsigned int> &l) {
    if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename list<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return (count_matching(p, *(d_a1)) + 1);
      } else {
        return count_matching(p, *(d_a1));
      }
    }
  }

  /// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
  __attribute__((pure)) static unsigned int
  categorize(const unsigned int &k, const list<unsigned int> &l);
  /// max_prefix_sum l maximum prefix sum (Kadane-like).
  __attribute__((pure)) static unsigned int
  max_prefix_sum(const list<unsigned int> &l);
  /// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
  __attribute__((pure)) static list<unsigned int>
  pairwise_sum(const list<unsigned int> &l);
  /// weighted_sum i l weighted sum with increasing weights.
  __attribute__((pure)) static unsigned int
  weighted_sum(unsigned int i, const list<unsigned int> &l);

  /// zip_with f l1 l2 zips two lists with a function.
  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  __attribute__((pure)) static list<T3> zip_with(F0 &&f, const list<T1> &l1,
                                                 const list<T2> &l2) {
    std::unique_ptr<list<T3>> _head{};
    std::unique_ptr<list<T3>> *_write = &_head;
    list<T2> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
        *(_write) = std::make_unique<list<T3>>(list<T3>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2.v())) {
          *(_write) = std::make_unique<list<T3>>(list<T3>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2.v());
          auto _cell = std::make_unique<list<T3>>(
              typename list<T3>::Cons(f(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<T3>::Cons>((*_write)->v_mut()).d_a1;
          list<T2> _next_l2 = *(d_a10);
          list<T1> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// zip_longest l1 l2 def zips with default for mismatched lengths.
  template <typename T1>
  __attribute__((pure)) static list<std::pair<T1, T1>>
  zip_longest_aux(const unsigned int &fuel, const list<T1> &l1,
                  const list<T1> &l2, const T1 default0) {
    std::unique_ptr<list<std::pair<T1, T1>>> _head{};
    std::unique_ptr<list<std::pair<T1, T1>>> *_write = &_head;
    list<T1> _loop_l2 = l2;
    list<T1> _loop_l1 = l1;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<list<std::pair<T1, T1>>>(
            list<std::pair<T1, T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1.v())) {
          if (std::holds_alternative<typename list<T1>::Nil>(_loop_l2.v())) {
            *(_write) = std::make_unique<list<std::pair<T1, T1>>>(
                list<std::pair<T1, T1>>::nil());
            break;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename list<T1>::Cons>(_loop_l2.v());
            auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(default0, d_a00), nullptr));
            *(_write) = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .d_a1;
            list<T1> _next_l2 = *(d_a10);
            list<T1> _next_l1 = list<T1>::nil();
            unsigned int _next_fuel = f;
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<T1>::Cons>(_loop_l1.v());
          if (std::holds_alternative<typename list<T1>::Nil>(_loop_l2.v())) {
            auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(d_a0, default0), nullptr));
            *(_write) = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .d_a1;
            list<T1> _next_l2 = list<T1>::nil();
            list<T1> _next_l1 = *(d_a1);
            unsigned int _next_fuel = f;
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename list<T1>::Cons>(_loop_l2.v());
            auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
                typename list<std::pair<T1, T1>>::Cons(
                    std::make_pair(d_a0, d_a00), nullptr));
            *(_write) = std::move(_cell);
            _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                          (*_write)->v_mut())
                          .d_a1;
            list<T1> _next_l2 = *(d_a10);
            list<T1> _next_l1 = *(d_a1);
            unsigned int _next_fuel = f;
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  __attribute__((pure)) static list<std::pair<T1, T1>>
  zip_longest(const list<T1> &l1, const list<T1> &l2, const T1 default0) {
    std::function<unsigned int(list<T1>)> length;
    length = [&](list<T1> l) -> unsigned int {
      struct _Enter {
        list<T1> l;
      };
      struct _Call1 {};
      using _Frame = std::variant<_Enter, _Call1>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{l});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          list<T1> l = _f.l;
          if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        } else {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = (_result + 1);
        }
      }
      return _result;
    };
    unsigned int len = (length(l1) + length(l2));
    return zip_longest_aux<T1>((len + 1), l1, l2, default0);
  }

  /// sliding_pairs l returns consecutive pairs: 1,2,3 -> (1,2),(2,3).
  template <typename T1>
  __attribute__((pure)) static list<std::pair<T1, T1>>
  sliding_pairs(const list<T1> &l) {
    std::unique_ptr<list<std::pair<T1, T1>>> _head{};
    std::unique_ptr<list<std::pair<T1, T1>>> *_write = &_head;
    list<T1> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        *(_write) = std::make_unique<list<std::pair<T1, T1>>>(
            list<std::pair<T1, T1>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
          *(_write) = std::make_unique<list<std::pair<T1, T1>>>(
              list<std::pair<T1, T1>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T1>::Cons>(_sv0.v());
          auto _cell = std::make_unique<list<std::pair<T1, T1>>>(
              typename list<std::pair<T1, T1>>::Cons(
                  std::make_pair(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<std::pair<T1, T1>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// partition3 p q l partitions into 3 groups based on 2 predicates.
  template <MapsTo<bool, unsigned int> F0, MapsTo<bool, unsigned int> F1>
  __attribute__((pure)) static std::pair<
      std::pair<list<unsigned int>, list<unsigned int>>, list<unsigned int>>
  partition3(F0 &&p, F1 &&q, const list<unsigned int> &l) {
    struct _Enter {
      const list<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
      F1 _s2;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::pair<list<unsigned int>, list<unsigned int>>,
              list<unsigned int>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<unsigned int> l = _f.l;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(std::make_pair(list<unsigned int>::nil(),
                                                  list<unsigned int>::nil()),
                                   list<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, p, q});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 p = _f._s1;
        F1 q = _f._s2;
        const std::pair<list<unsigned int>, list<unsigned int>> &p0 =
            _result.first;
        const list<unsigned int> &cs = _result.second;
        const list<unsigned int> &as_ = p0.first;
        const list<unsigned int> &bs = p0.second;
        if (p(d_a0)) {
          _result = std::make_pair(
              std::make_pair(list<unsigned int>::cons(d_a0, as_), bs), cs);
        } else {
          if (q(d_a0)) {
            _result = std::make_pair(
                std::make_pair(as_, list<unsigned int>::cons(d_a0, bs)), cs);
          } else {
            _result = std::make_pair(std::make_pair(as_, bs),
                                     list<unsigned int>::cons(d_a0, cs));
          }
        }
      }
    }
    return _result;
  }

  /// transpose m transposes a matrix (list of lists).
  template <typename T1>
  __attribute__((pure)) static list<list<T1>>
  transpose_fuel(const unsigned int &fuel, const list<list<T1>> &m) {
    std::unique_ptr<list<list<T1>>> _head{};
    std::unique_ptr<list<list<T1>>> *_write = &_head;
    list<list<T1>> _loop_m = m;
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        std::function<list<T1>(list<list<T1>>)> map_head;
        map_head = [&](list<list<T1>> l) -> list<T1> {
          struct _Enter {
            list<list<T1>> l;
          };
          struct _Call1 {
            T1 _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          list<T1> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{l});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              list<list<T1>> l = _f.l;
              if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
                _result = list<T1>::nil();
              } else {
                const auto &[d_a0, d_a1] =
                    std::get<typename list<list<T1>>::Cons>(l.v());
                if (std::holds_alternative<typename list<T1>::Nil>(d_a0.v())) {
                  _result = list<T1>::nil();
                } else {
                  const auto &[d_a00, d_a10] =
                      std::get<typename list<T1>::Cons>(d_a0.v());
                  _stack.emplace_back(_Call1{d_a00});
                  _stack.emplace_back(_Enter{*(d_a1)});
                }
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = list<T1>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        std::function<list<list<T1>>(list<list<T1>>)> map_tail;
        map_tail = [&](list<list<T1>> l) -> list<list<T1>> {
          struct _Enter {
            list<list<T1>> l;
          };
          struct _Call1 {
            list<T1> _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          list<list<T1>> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{l});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              list<list<T1>> l = _f.l;
              if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
                _result = list<list<T1>>::nil();
              } else {
                const auto &[d_a00, d_a10] =
                    std::get<typename list<list<T1>>::Cons>(l.v());
                if (std::holds_alternative<typename list<T1>::Nil>(d_a00.v())) {
                  _result = list<list<T1>>::nil();
                } else {
                  const auto &[d_a01, d_a11] =
                      std::get<typename list<T1>::Cons>(d_a00.v());
                  _stack.emplace_back(_Call1{*(d_a11)});
                  _stack.emplace_back(_Enter{*(d_a10)});
                }
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = list<list<T1>>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        if (std::holds_alternative<typename list<list<T1>>::Nil>(_loop_m.v())) {
          *(_write) = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename list<list<T1>>::Cons>(_loop_m.v());
          if (std::holds_alternative<typename list<T1>::Nil>(d_a01.v())) {
            *(_write) = std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
            break;
          } else {
            list<T1> heads = map_head(_loop_m);
            list<list<T1>> tails0 = map_tail(_loop_m);
            if (std::holds_alternative<typename list<T1>::Nil>(heads.v())) {
              *(_write) =
                  std::make_unique<list<list<T1>>>(list<list<T1>>::nil());
              break;
            } else {
              auto _cell = std::make_unique<list<list<T1>>>(
                  typename list<list<T1>>::Cons(heads, nullptr));
              *(_write) = std::move(_cell);
              _write =
                  &std::get<typename list<list<T1>>::Cons>((*_write)->v_mut())
                       .d_a1;
              list<list<T1>> _next_m = tails0;
              unsigned int _next_fuel = f;
              _loop_m = std::move(_next_m);
              _loop_fuel = std::move(_next_fuel);
              continue;
            }
          }
        }
      }
    }
    return std::move(*(_head));
  }

  template <typename T1>
  __attribute__((pure)) static list<list<T1>>
  transpose(const list<list<T1>> &m) {
    return transpose_fuel<T1>(100u, m);
  }

  /// map_accum_l f acc l maps with accumulator from left.
  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<T3, list<T2>>
  map_accum_l(F0 &&f, const T3 acc, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
      const T3 acc;
    };

    struct _Call1 {
      T2 _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<T3, list<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        const T3 acc = _f.acc;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(acc, list<T2>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          auto _cs = f(acc, d_a0);
          const T3 &acc_ = _cs.first;
          const T2 &y = _cs.second;
          _stack.emplace_back(_Call1{y});
          _stack.emplace_back(_Enter{*(d_a1), acc_});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T2 y = _f._s0;
        const T3 &acc__ = _result.first;
        const list<T2> &ys = _result.second;
        _result = std::make_pair(acc__, list<T2>::cons(y, ys));
      }
    }
    return _result;
  }

  /// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
  __attribute__((pure)) static list<unsigned int>
  prefix_sums(unsigned int acc, const list<unsigned int> &l);
  /// uniq_sorted l removes consecutive duplicates from sorted list.
  __attribute__((pure)) static list<unsigned int>
  uniq_sorted(const list<unsigned int> &l);
  /// Helper: take first n elements.
  __attribute__((pure)) static list<unsigned int>
  take_n(const unsigned int &n, const list<unsigned int> &l);
  /// Helper: list length.
  __attribute__((pure)) static unsigned int
  len_list(const list<unsigned int> &l);
  /// windows n l returns all sliding windows of size n.
  __attribute__((pure)) static list<list<unsigned int>>
  windows_aux(const unsigned int &fuel, const unsigned int &n,
              const list<unsigned int> &l);
  __attribute__((pure)) static list<list<unsigned int>>
  windows(const unsigned int &n, const list<unsigned int> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  __attribute__((pure)) static bool is_prefix_of(const list<unsigned int> &l1,
                                                 const list<unsigned int> &l2);
  /// lookup_all key l finds all values for key in association list.
  __attribute__((pure)) static list<unsigned int>
  lookup_all(const unsigned int &key,
             const list<std::pair<unsigned int, unsigned int>> &l);

  /// delete_by eq x l deletes first element equal to x by custom equality.
  template <MapsTo<bool, unsigned int, unsigned int> F0>
  __attribute__((pure)) static list<unsigned int>
  delete_by(F0 &&eq, const unsigned int &x, const list<unsigned int> &l) {
    std::unique_ptr<list<unsigned int>> _head{};
    std::unique_ptr<list<unsigned int>> *_write = &_head;
    list<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<list<unsigned int>>(list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<unsigned int>::Cons>(_loop_l.v());
        if (eq(x, d_a0)) {
          *(_write) = std::make_unique<list<unsigned int>>(*(d_a1));
          break;
        } else {
          auto _cell = std::make_unique<list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// find_indices p l returns list of indices where predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static list<unsigned int>
  find_indices_aux(F0 &&p, const list<unsigned int> &l, unsigned int i) {
    if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
      return list<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename list<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return list<unsigned int>::cons(i,
                                        find_indices_aux(p, *(d_a1), (i + 1)));
      } else {
        return find_indices_aux(p, *(d_a1), (i + 1));
      }
    }
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static list<unsigned int>
  find_indices(F0 &&p, const list<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }

  /// member x l checks if x is in the list.
  __attribute__((pure)) static bool member(const unsigned int &x,
                                           const list<unsigned int> &l);
  /// product l multiplies all elements in the list.
  __attribute__((pure)) static unsigned int
  product(const list<unsigned int> &l);
  /// sum_list l sums all elements in the list.
  __attribute__((pure)) static unsigned int
  sum_list(const list<unsigned int> &l);

  /// flatten l flattens a list of lists.
  template <typename T1>
  __attribute__((pure)) static list<T1> flatten(const list<list<T1>> &l) {
    struct _Enter {
      const list<list<T1>> l;
    };

    struct _Call1 {
      list<T1> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<list<T1>> l = _f.l;
        if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<list<T1>>::Cons>(l.v());
          list<list<T1>> d_a1_value = *(d_a1);
          std::function<list<T1>(list<T1>, list<T1>)> app;
          app = [&](list<T1> l1, list<T1> l2) -> list<T1> {
            struct _Enter {
              list<T1> l1;
            };
            struct _Call1 {
              T1 _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            list<T1> _result{};
            std::vector<_Frame> _stack;
            _stack.reserve(16);
            _stack.emplace_back(_Enter{l1});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                auto _f = std::move(std::get<_Enter>(_frame));
                list<T1> l1 = _f.l1;
                if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
                  _result = l2;
                } else {
                  const auto &[d_a00, d_a10] =
                      std::get<typename list<T1>::Cons>(l1.v());
                  _stack.emplace_back(_Call1{d_a00});
                  _stack.emplace_back(_Enter{*(d_a10)});
                }
              } else {
                auto _f = std::move(std::get<_Call1>(_frame));
                _result = list<T1>::cons(_f._s0, _result);
              }
            }
            return _result;
          };
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1_value});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = app(_f._s0, _result);
      }
    }
    return _result;
  }

  /// flatten_nested l alternative flatten with different pattern: flattens one
  /// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
  /// :: flatten (xs :: rest).
  __attribute__((pure)) static list<unsigned int>
  flatten_nested_fuel(const unsigned int &fuel,
                      const list<list<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  sum_list_lengths(const list<list<unsigned int>> &l);
  __attribute__((pure)) static list<unsigned int> flatten_nested(
      const list<list<unsigned int>> &l); /// compress l removes consecutive
                                          /// duplicates: 1,1,2,2,2,3 -> 1,2,3.
  __attribute__((pure)) static list<unsigned int>
  compress(const list<unsigned int> &l);
  /// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
  /// (1,2),(3,4).
  __attribute__((pure)) static list<std::pair<unsigned int, unsigned int>>
  group_pairs(const list<unsigned int> &l);
  /// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  swizzle(const list<unsigned int> &l);
  /// index_of_aux x l i finds first index of x in l starting from i.
  __attribute__((pure)) static unsigned int
  index_of_aux(const unsigned int &x, const list<unsigned int> &l,
               unsigned int i);
  __attribute__((pure)) static unsigned int
  index_of(const unsigned int &x, const list<unsigned int> &l);
  /// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
  __attribute__((pure)) static list<unsigned int>
  interleave(list<unsigned int> l1, list<unsigned int> l2);
  /// lookup key l finds value for key in association list.
  __attribute__((pure)) static unsigned int
  lookup(const unsigned int &key,
         const list<std::pair<unsigned int, unsigned int>> &l);
  /// group l groups consecutive equal elements: 1,1,2,2,2,3 ->
  /// [1,1],[2,2,2],[3].
  __attribute__((pure)) static list<list<unsigned int>>
  group_fuel(const unsigned int &fuel, const list<unsigned int> &l);
  __attribute__((pure)) static list<list<unsigned int>>
  group(const list<unsigned int> &l);
  /// Internal helper: reverse a list.
  __attribute__((pure)) static list<unsigned int>
  rev_helper(list<unsigned int> acc, const list<unsigned int> &l);
  /// reverse_insert x l inserts x and reverses at each step.
  __attribute__((pure)) static list<unsigned int>
  reverse_insert(unsigned int x, const list<unsigned int> &l);
  /// Internal helper: append lists.
  __attribute__((pure)) static list<unsigned int>
  app_helper(const list<unsigned int> &l1, list<unsigned int> l2);
  /// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
  __attribute__((pure)) static list<unsigned int>
  double_append(const list<unsigned int> &l1, list<unsigned int> l2);
  /// remove_if_sum_even l removes element if sum with next is even.
  __attribute__((pure)) static list<unsigned int>
  remove_if_sum_even(const list<unsigned int> &l);
  /// split_at n l splits list at index n into (prefix, suffix).
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  split_at(const unsigned int &n, list<unsigned int> l);

  /// span p l splits list at first element not satisfying p.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  span(F0 &&p, list<unsigned int> l) {
    struct _Enter {
      list<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<list<unsigned int>, list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<unsigned int> l = _f.l;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(list<unsigned int>::nil(),
                                   list<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          } else {
            _result = std::make_pair(list<unsigned int>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        const list<unsigned int> &a = _result.first;
        const list<unsigned int> &b = _result.second;
        _result = std::make_pair(list<unsigned int>::cons(d_a0, a), b);
      }
    }
    return _result;
  }

  /// unzip l splits list of pairs into two lists.
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  unzip(const list<std::pair<unsigned int, unsigned int>> &l);
  /// nth n l default returns nth element or default if out of bounds.
  __attribute__((pure)) static unsigned int nth(const unsigned int &n,
                                                const list<unsigned int> &l,
                                                unsigned int default0);
  /// last l default returns last element or default if empty.
  __attribute__((pure)) static unsigned int last(const list<unsigned int> &l,
                                                 unsigned int default0);
  /// drop n l drops first n elements.
  __attribute__((pure)) static list<unsigned int> drop(const unsigned int &n,
                                                       list<unsigned int> l);
  /// init l returns all but last element.
  __attribute__((pure)) static list<unsigned int>
  init(const list<unsigned int> &l);
  /// count x l counts occurrences of x in l.
  __attribute__((pure)) static unsigned int count(const unsigned int &x,
                                                  const list<unsigned int> &l);
  /// maximum l finds maximum element (returns 0 for empty list).
  __attribute__((pure)) static unsigned int
  maximum(const list<unsigned int> &l);
  /// minmax l finds both minimum and maximum in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  minmax(const list<unsigned int> &l);
  /// Helper for rotate_left.
  __attribute__((pure)) static list<unsigned int>
  rotate_left_fuel(const unsigned int &fuel, const unsigned int &n,
                   list<unsigned int> l);
  /// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
  /// 3,4,1,2.
  __attribute__((pure)) static list<unsigned int>
  rotate_left(unsigned int n, const list<unsigned int> &l);
  /// intercalate sep lists joins lists with separator: intercalate 0
  /// [1,2],[3,4] -> 1,2,0,3,4.
  __attribute__((pure)) static list<unsigned int>
  intercalate(const list<unsigned int> &sep,
              const list<list<unsigned int>> &lists);
  /// majority l finds majority element using Boyer-Moore voting algorithm.
  /// Returns (candidate, count).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  majority(const list<unsigned int> &l);
  /// zip3 l1 l2 l3 zips three lists into triples.
  __attribute__((pure)) static list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
  zip3(const list<unsigned int> &l1, const list<unsigned int> &l2,
       const list<unsigned int> &l3);
  /// sum_and_count l returns both sum and count in one pass.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  sum_and_count(const list<unsigned int> &l);
  /// elem_at n l returns element at index n (like nth but with different name).
  __attribute__((pure)) static std::optional<unsigned int>
  elem_at(const unsigned int &n, const list<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_LISTS
