#ifndef INCLUDED_LOOPIFY_LISTS
#define INCLUDED_LOOPIFY_LISTS

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
struct LoopifyLists {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a, l] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a.type() == typeid(A))
                  return std::any_cast<A>(a);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a);
              } else
                return A(a);
            }(),
            l ? std::make_shared<list<A>>(*l) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list(Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l) {
            _stack.push_back(std::move(_alt->l));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.f0)(std::move(_f.a0), std::move(_f.a1),
                                   std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(T2 f, F1 &&f0,
           const list<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.f0)(std::move(_f.a0), std::move(_f.a1),
                                   std::move(_result));
      }
    }
    return _result;
  }

  /// stutter l duplicates each element: 1,2 -> 1,1,2,2.
  template <typename T1>
  static list<T1>
  stutter(const list<T1> &l) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [a0_0, a0_1], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      T1 a0_0;
      T1 a0_1;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified stutter: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T1>::cons(
            std::move(_f.a0_0),
            list<T1>::cons(std::move(_f.a0_1), std::move(_result)));
      }
    }
    return _result;
  }

  /// snoc l x appends x at the end (reverse cons).
  template <typename T1>
  static list<T1>
  snoc(const list<T1> &l,
       T1 x) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified snoc: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T1>::cons(x, list<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T1>::cons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  /// intersperse sep l inserts separator between elements.
  template <typename T1>
  static list<T1>
  intersperse(T1 sep,
              const list<T1> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [a0, sep], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      T1 a0;
      T1 sep;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified intersperse: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename list<T1>::Nil>(_sv.v())) {
            _result = list<T1>::cons(a0, list<T1>::nil());
          } else {
            _stack.emplace_back(_Resume_Cons{a0, sep});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T1>::cons(
            std::move(_f.a0),
            list<T1>::cons(std::move(_f.sep), std::move(_result)));
      }
    }
    return _result;
  } /// replicate n x creates n copies of x.

  template <typename T1>
  static list<T1> replicate(
      uint64_t n,
      T1 x) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      uint64_t n;
    };

    /// _Resume_m: saves [x], resumes after recursive call with _result.
    struct _Resume_m {
      T1 x;
    };

    using _Frame = std::variant<_Enter, _Resume_m>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified replicate: _Enter -> _Resume_m.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = list<T1>::nil();
        } else {
          uint64_t m = n - 1;
          _stack.emplace_back(_Resume_m{x});
          _stack.emplace_back(_Enter{m});
        }
      } else {
        auto _f = std::move(std::get<_Resume_m>(_frame));
        _result = list<T1>::cons(std::move(_f.x), std::move(_result));
      }
    }
    return _result;
  }

  /// replicate_list n l repeats list l n times.
  template <typename T1>
  static list<T1>
  replicate_list(uint64_t n,
                 const list<T1> &l) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      uint64_t n;
    };

    /// _Resume_m: saves [app, l], resumes after recursive call with _result.
    struct _Resume_m {
      std::function<list<T1>(list<T1>, list<T1>)> app;
      list<T1> l;
    };

    using _Frame = std::variant<_Enter, _Resume_m>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified replicate_list: _Enter -> _Resume_m.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t n = _f.n;
        auto app_impl = [](auto &_self_app, const list<T1> &l1,
                           list<T1> l2) -> list<T1> {
          if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
            return l2;
          } else {
            const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
            return list<T1>::cons(a0, _self_app(_self_app, *a1, std::move(l2)));
          }
        };
        auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
          return app_impl(app_impl, l1, l2);
        };
        if (n <= 0) {
          _result = list<T1>::nil();
        } else {
          uint64_t m = n - 1;
          _stack.emplace_back(_Resume_m{std::move(app), l});
          _stack.emplace_back(_Enter{m});
        }
      } else {
        auto _f = std::move(std::get<_Resume_m>(_frame));
        _result = std::move(_f.app)(std::move(_f.l), std::move(_result));
      }
    }
    return _result;
  }

  /// init_list n f generates f 0, f 1, ..., f (n-1).
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static list<T1> init_list(uint64_t n, F1 &&f) {
    auto go_impl = [&](auto &_self_go, uint64_t i) -> list<T1> {
      if (i <= 0) {
        return list<T1>::nil();
      } else {
        uint64_t j = i - 1;
        return list<T1>::cons(f((((n - i) > n ? 0 : (n - i)))),
                              _self_go(_self_go, j));
      }
    };
    auto go = [&](uint64_t i) -> list<T1> { return go_impl(go_impl, i); };
    return go(n);
  }

  /// range start count generates start, start+1, ..., start+count-1.
  static list<uint64_t> range(uint64_t start, uint64_t count0);

  /// tails l returns all suffixes.
  template <typename T1>
  static list<list<T1>>
  tails(list<T1> l) { /// _Enter: captures varying parameters for each recursive
                      /// call.

    struct _Enter {
      list<T1> l;
    };

    /// _Resume_Cons: saves [l], resumes after recursive call with _result.
    struct _Resume_Cons {
      list<T1> l;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l)});
    /// Loopified tails: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<T1> l = std::move(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v_mut())) {
          _result =
              list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil());
        } else {
          auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v_mut());
          _stack.emplace_back(_Resume_Cons{l});
          _stack.emplace_back(_Enter{*a1});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<list<T1>>::cons(std::move(_f.l), std::move(_result));
      }
    }
    return _result;
  }

  /// inits l returns all prefixes (complex recursion pattern).
  template <typename T1>
  static list<list<T1>>
  inits(const list<T1> &l) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [_s0, map_cons], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      std::decay_t<decltype(list<T1>::nil())> _s0;
      std::function<list<list<T1>>(list<list<T1>>)> map_cons;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified inits: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result =
              list<list<T1>>::cons(list<T1>::nil(), list<list<T1>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto map_cons_impl = [&](auto &_self_map_cons,
                                   const list<list<T1>> &ys) -> list<list<T1>> {
            if (std::holds_alternative<typename list<list<T1>>::Nil>(ys.v())) {
              return list<list<T1>>::nil();
            } else {
              const auto &[a2, a3] =
                  std::get<typename list<list<T1>>::Cons>(ys.v());
              return list<list<T1>>::cons(list<T1>::cons(a0, a2),
                                          _self_map_cons(_self_map_cons, *a3));
            }
          };
          auto map_cons = [&](const list<list<T1>> &ys) -> list<list<T1>> {
            return map_cons_impl(map_cons_impl, ys);
          };
          _stack.emplace_back(
              _Resume_Cons{list<T1>::nil(), std::move(map_cons)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<list<T1>>::cons(
            _f._s0, std::move(_f.map_cons)(std::move(_result)));
      }
    }
    return _result;
  }

  /// scanl f acc l returns intermediate fold results.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &, T1 &>
  static list<T2>
  scanl(F0 &&f, T2 acc,
        const list<T1> &l) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const list<T1> *l;
      T2 acc;
    };

    /// _Resume_Cons: saves [acc], resumes after recursive call with _result.
    struct _Resume_Cons {
      T2 acc;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified scanl: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        auto acc = std::move(_f.acc);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<T2>::cons(acc, list<T2>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          T2 new_acc = f(acc, a0);
          _stack.emplace_back(_Resume_Cons{acc});
          _stack.emplace_back(_Enter{a1.get(), std::move(new_acc)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T2>::cons(std::move(_f.acc), std::move(_result));
      }
    }
    return _result;
  }

  /// group_by eq l groups consecutive equal elements.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static list<list<T1>>
  group_by_aux(F0 &&eq, const T1 &prev, list<T1> acc,
               const list<T1> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const list<T1> *l;
      list<T1> acc;
      T1 prev;
    };

    /// _Resume1: saves [_s0], resumes after recursive call with _result.
    struct _Resume1 {
      list<T1> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, std::move(acc), prev});
    /// Loopified group_by_aux: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        list<T1> acc = std::move(_f.acc);
        const T1 prev = std::move(_f.prev);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<list<T1>>::cons(std::move(acc), list<list<T1>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          if (eq(prev, a0)) {
            _stack.emplace_back(
                _Enter{a1.get(), list<T1>::cons(a0, std::move(acc)), a0});
          } else {
            _stack.emplace_back(_Resume1{std::move(std::move(acc))});
            _stack.emplace_back(
                _Enter{a1.get(), list<T1>::cons(a0, list<T1>::nil()), a0});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<list<T1>>::cons(std::move(_f._s0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static list<list<T1>> group_by(F0 &&eq, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<list<T1>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return group_by_aux<T1>(eq, a0, list<T1>::cons(a0, list<T1>::nil()), *a1);
    }
  } /// chunks_of n l splits into chunks of size n.

  template <typename T1>
  static list<list<T1>>
  chunks_of_aux(uint64_t n, const list<T1> &l,
                uint64_t fuel) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      uint64_t fuel;
      list<T1> l;
    };

    /// _Resume_Cons: saves [chunk], resumes after recursive call with _result.
    struct _Resume_Cons {
      list<T1> chunk;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{fuel, l});
    /// Loopified chunks_of_aux: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t fuel = _f.fuel;
        const list<T1> &l = std::move(_f.l);
        if (fuel <= 0) {
          _result = list<list<T1>>::nil();
        } else {
          uint64_t f = fuel - 1;
          auto take_impl = [](auto &_self_take, uint64_t k,
                              const list<T1> &lst) -> list<T1> {
            if (k <= 0) {
              return list<T1>::nil();
            } else {
              uint64_t m = k - 1;
              if (std::holds_alternative<typename list<T1>::Nil>(lst.v())) {
                return list<T1>::nil();
              } else {
                const auto &[a0, a1] =
                    std::get<typename list<T1>::Cons>(lst.v());
                return list<T1>::cons(a0, _self_take(_self_take, m, *a1));
              }
            }
          };
          auto take = [&](uint64_t k, const list<T1> &lst) -> list<T1> {
            return take_impl(take_impl, k, lst);
          };
          auto drop0_impl = [](auto &_self_drop0, uint64_t k,
                               list<T1> lst) -> list<T1> {
            if (k <= 0) {
              return lst;
            } else {
              uint64_t m = k - 1;
              if (std::holds_alternative<typename list<T1>::Nil>(lst.v_mut())) {
                return list<T1>::nil();
              } else {
                auto &[a00, a10] =
                    std::get<typename list<T1>::Cons>(lst.v_mut());
                return _self_drop0(_self_drop0, m, *a10);
              }
            }
          };
          auto drop0 = [&](uint64_t k, list<T1> lst) -> list<T1> {
            return drop0_impl(drop0_impl, k, lst);
          };
          if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
            _result = list<list<T1>>::nil();
          } else {
            list<T1> chunk = take(n, l);
            list<T1> rest = drop0(n, l);
            if (std::holds_alternative<typename list<T1>::Nil>(chunk.v_mut())) {
              _result = list<list<T1>>::nil();
            } else {
              _stack.emplace_back(_Resume_Cons{chunk});
              _stack.emplace_back(_Enter{f, std::move(rest)});
            }
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<list<T1>>::cons(std::move(_f.chunk), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1>
  static list<list<T1>> chunks_of(uint64_t n, const list<T1> &l) {
    auto length_impl = [](auto &_self_length, const list<T1> &l0) -> uint64_t {
      if (std::holds_alternative<typename list<T1>::Nil>(l0.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l0.v());
        return (_self_length(_self_length, *a1) + 1);
      }
    };
    auto length = [&](const list<T1> &l0) -> uint64_t {
      return length_impl(length_impl, l0);
    };
    return chunks_of_aux<T1>(n, l, (length(l) + 1));
  }

  /// step_sum l sums with conditional contributions: even values as-is, odd
  /// doubled.
  static uint64_t step_sum(const list<uint64_t> &l);
  /// sum_abs l sums absolute values (using monus for nat).
  static uint64_t sum_abs(const list<uint64_t> &l, uint64_t base);
  /// four_elem l multi-case pattern matching on list structure.
  static uint64_t four_elem(const list<uint64_t> &l);
  /// between lo hi l filters elements in range lo, hi.
  static list<uint64_t> between(uint64_t lo, uint64_t hi,
                                const list<uint64_t> &l);

  /// count_matching p l counts elements satisfying predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t count_matching(
      F0 &&p,
      const list<uint64_t>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
    };

    /// _Resume1: resumes after recursive call with _result.
    struct _Resume1 {};

    using _Frame = std::variant<_Enter, _Resume1>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified count_matching: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  /// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
  static uint64_t categorize(uint64_t k, const list<uint64_t> &l);
  /// max_prefix_sum l maximum prefix sum (Kadane-like).
  static uint64_t max_prefix_sum(const list<uint64_t> &l);
  /// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
  static list<uint64_t> pairwise_sum(const list<uint64_t> &l);
  /// weighted_sum i l weighted sum with increasing weights.
  static uint64_t weighted_sum(uint64_t i, const list<uint64_t> &l);

  /// zip_with f l1 l2 zips two lists with a function.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static list<T3>
  zip_with(F0 &&f, const list<T1> &l1,
           const list<T2> &l2) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T2> *l2;
      const list<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      T3 _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T3> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l2, &l1});
    /// Loopified zip_with: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T2> &l2 = *_f.l2;
        const list<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
          _result = list<T3>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
          if (std::holds_alternative<typename list<T2>::Nil>(l2.v())) {
            _result = list<T3>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename list<T2>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons{f(a0, a00)});
            _stack.emplace_back(_Enter{a10.get(), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<T3>::cons(std::move(_f._s0), std::move(_result));
      }
    }
    return _result;
  }

  /// zip_longest l1 l2 def zips with default for mismatched lengths.
  template <typename T1>
  static list<std::pair<T1, T1>>
  zip_longest_aux(uint64_t fuel, const list<T1> &l1, const list<T1> &l2,
                  T1 default0) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      list<T1> l2;
      list<T1> l1;
      uint64_t fuel;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(std::make_pair(std::declval<T1 &>(),
                                           std::declval<T1 &>()))>
          _s0;
    };

    /// _Resume_Cons_1: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons_1 {
      std::decay_t<decltype(std::make_pair(std::declval<T1 &>(),
                                           std::declval<T1 &>()))>
          _s0;
    };

    /// _Resume_Nil: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Nil {
      std::decay_t<decltype(std::make_pair(std::declval<T1 &>(),
                                           std::declval<T1 &>()))>
          _s0;
    };

    using _Frame =
        std::variant<_Enter, _Resume_Cons, _Resume_Cons_1, _Resume_Nil>;
    list<std::pair<T1, T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l2, l1, fuel});
    /// Loopified zip_longest_aux: _Enter -> _Resume_Cons -> _Resume_Cons_1 ->
    /// _Resume_Nil.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l2 = std::move(_f.l2);
        const list<T1> &l1 = std::move(_f.l1);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = list<std::pair<T1, T1>>::nil();
        } else {
          uint64_t f = fuel - 1;
          if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
            if (std::holds_alternative<typename list<T1>::Nil>(l2.v())) {
              _result = list<std::pair<T1, T1>>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<T1>::Cons>(l2.v());
              _stack.emplace_back(_Resume_Cons{std::make_pair(default0, a00)});
              _stack.emplace_back(_Enter{*a10, list<T1>::nil(), f});
            }
          } else {
            const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l1.v());
            if (std::holds_alternative<typename list<T1>::Nil>(l2.v())) {
              _stack.emplace_back(_Resume_Nil{std::make_pair(a0, default0)});
              _stack.emplace_back(_Enter{list<T1>::nil(), *a1, f});
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<T1>::Cons>(l2.v());
              _stack.emplace_back(_Resume_Cons_1{std::make_pair(a0, a00)});
              _stack.emplace_back(_Enter{*a10, *a1, f});
            }
          }
        }
      } else if (std::holds_alternative<_Resume_Cons>(_frame)) {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<std::pair<T1, T1>>::cons(_f._s0, std::move(_result));
      } else if (std::holds_alternative<_Resume_Cons_1>(_frame)) {
        auto _f = std::move(std::get<_Resume_Cons_1>(_frame));
        _result = list<std::pair<T1, T1>>::cons(_f._s0, std::move(_result));
      } else {
        auto _f = std::move(std::get<_Resume_Nil>(_frame));
        _result = list<std::pair<T1, T1>>::cons(_f._s0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1>
  static list<std::pair<T1, T1>>
  zip_longest(const list<T1> &l1, const list<T1> &l2, const T1 &default0) {
    auto length_impl = [](auto &_self_length, const list<T1> &l) -> uint64_t {
      if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
        return (_self_length(_self_length, *a1) + 1);
      }
    };
    auto length = [&](const list<T1> &l) -> uint64_t {
      return length_impl(length_impl, l);
    };
    uint64_t len = (length(l1) + length(l2));
    return zip_longest_aux<T1>((len + 1), l1, l2, default0);
  }

  /// sliding_pairs l returns consecutive pairs: 1,2,3 -> (1,2),(2,3).
  template <typename T1>
  static list<std::pair<T1, T1>>
  sliding_pairs(const list<T1> &l) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(std::make_pair(std::declval<T1 &>(),
                                           std::declval<T1 &>()))>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<std::pair<T1, T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified sliding_pairs: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<std::pair<T1, T1>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
            _result = list<std::pair<T1, T1>>::nil();
          } else {
            const auto &[a00, a10] =
                std::get<typename list<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a00)});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<std::pair<T1, T1>>::cons(_f._s0, std::move(_result));
      }
    }
    return _result;
  }

  /// partition3 p q l partitions into 3 groups based on 2 predicates.
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &> &&
             std::is_invocable_r_v<bool, F1 &, uint64_t &>
  static std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
  partition3(F0 &&p, F1 &&q,
             const list<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, p, q], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 p;
      F1 q;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition3: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()),
              list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p, q});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        auto p = std::move(_f.p);
        auto q = std::move(_f.q);
        auto _cs = std::move(_result);
        std::pair<list<uint64_t>, list<uint64_t>> p0 = std::move(_cs.first);
        list<uint64_t> cs = std::move(_cs.second);
        list<uint64_t> as_ = std::move(p0.first);
        list<uint64_t> bs = std::move(p0.second);
        if (p(a0)) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::cons(a0, std::move(as_)),
                             std::move(bs)),
              std::move(cs));
        } else {
          if (q(a0)) {
            _result = std::make_pair(
                std::make_pair(std::move(as_),
                               list<uint64_t>::cons(a0, std::move(bs))),
                std::move(cs));
          } else {
            _result =
                std::make_pair(std::make_pair(std::move(as_), std::move(bs)),
                               list<uint64_t>::cons(a0, std::move(cs)));
          }
        }
      }
    }
    return _result;
  }

  /// transpose m transposes a matrix (list of lists).
  template <typename T1>
  static list<list<T1>> transpose_fuel(
      uint64_t fuel,
      const list<list<T1>>
          &m) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      list<list<T1>> m;
      uint64_t fuel;
    };

    /// _Resume_Cons: saves [heads], resumes after recursive call with _result.
    struct _Resume_Cons {
      list<T1> heads;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{m, fuel});
    /// Loopified transpose_fuel: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<list<T1>> &m = std::move(_f.m);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = list<list<T1>>::nil();
        } else {
          uint64_t f = fuel - 1;
          auto map_head_impl = [](auto &_self_map_head,
                                  const list<list<T1>> &l) -> list<T1> {
            if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
              return list<T1>::nil();
            } else {
              const auto &[a0, a1] =
                  std::get<typename list<list<T1>>::Cons>(l.v());
              if (std::holds_alternative<typename list<T1>::Nil>(a0.v())) {
                return list<T1>::nil();
              } else {
                const auto &[a00, a10] =
                    std::get<typename list<T1>::Cons>(a0.v());
                return list<T1>::cons(a00, _self_map_head(_self_map_head, *a1));
              }
            }
          };
          auto map_head = [&](const list<list<T1>> &l) -> list<T1> {
            return map_head_impl(map_head_impl, l);
          };
          auto map_tail_impl = [](auto &_self_map_tail,
                                  const list<list<T1>> &l) -> list<list<T1>> {
            if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
              return list<list<T1>>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<list<T1>>::Cons>(l.v());
              if (std::holds_alternative<typename list<T1>::Nil>(a00.v())) {
                return list<list<T1>>::nil();
              } else {
                const auto &[a01, a11] =
                    std::get<typename list<T1>::Cons>(a00.v());
                return list<list<T1>>::cons(
                    *a11, _self_map_tail(_self_map_tail, *a10));
              }
            }
          };
          auto map_tail = [&](const list<list<T1>> &l) -> list<list<T1>> {
            return map_tail_impl(map_tail_impl, l);
          };
          if (std::holds_alternative<typename list<list<T1>>::Nil>(m.v())) {
            _result = list<list<T1>>::nil();
          } else {
            const auto &[a01, a11] =
                std::get<typename list<list<T1>>::Cons>(m.v());
            if (std::holds_alternative<typename list<T1>::Nil>(a01.v())) {
              _result = list<list<T1>>::nil();
            } else {
              list<T1> heads = map_head(m);
              list<list<T1>> tails0 = map_tail(m);
              if (std::holds_alternative<typename list<T1>::Nil>(
                      heads.v_mut())) {
                _result = list<list<T1>>::nil();
              } else {
                _stack.emplace_back(_Resume_Cons{heads});
                _stack.emplace_back(_Enter{std::move(tails0), f});
              }
            }
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<list<T1>>::cons(std::move(_f.heads), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1>
  static list<list<T1>> transpose(const list<list<T1>> &m) {
    return transpose_fuel<T1>(UINT64_C(100), m);
  }

  /// map_accum_l f acc l maps with accumulator from left.
  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<T3, list<T2>>
  map_accum_l(F0 &&f, T3 acc,
              const list<T1> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const list<T1> *l;
      T3 acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      T2 y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<T3, list<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified map_accum_l: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        auto acc = std::move(_f.acc);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(std::move(acc), list<T2>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto _cs = f(acc, a0);
          T3 acc_ = std::move(_cs.first);
          T2 y = std::move(_cs.second);
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{a1.get(), std::move(acc_)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        auto y = std::move(_f.y);
        auto _cs1 = std::move(_result);
        T3 acc__ = std::move(_cs1.first);
        list<T2> ys = std::move(_cs1.second);
        _result =
            std::make_pair(std::move(acc__), list<T2>::cons(y, std::move(ys)));
      }
    }
    return _result;
  }

  /// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
  static list<uint64_t> prefix_sums(uint64_t acc, const list<uint64_t> &l);
  /// uniq_sorted l removes consecutive duplicates from sorted list.
  static list<uint64_t> uniq_sorted(const list<uint64_t> &l);
  /// Helper: take first n elements.
  static list<uint64_t> take_n(uint64_t n, const list<uint64_t> &l);
  /// Helper: list length.
  static uint64_t len_list(const list<uint64_t> &l);
  /// windows n l returns all sliding windows of size n.
  static list<list<uint64_t>> windows_aux(uint64_t fuel, uint64_t n,
                                          const list<uint64_t> &l);
  static list<list<uint64_t>> windows(uint64_t n, const list<uint64_t> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const list<uint64_t> &l1, const list<uint64_t> &l2);
  /// lookup_all key l finds all values for key in association list.
  static list<uint64_t>
  lookup_all(uint64_t key, const list<std::pair<uint64_t, uint64_t>> &l);

  /// delete_by eq x l deletes first element equal to x by custom equality.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static list<uint64_t>
  delete_by(F0 &&eq, uint64_t x,
            const list<uint64_t> &l) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    list<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified delete_by: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (eq(x, a0)) {
            _result = *a1;
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<uint64_t>::cons(_f.a0, std::move(_result));
      }
    }
    return _result;
  }

  /// find_indices p l returns list of indices where predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static list<uint64_t>
  find_indices_aux(F0 &&p, const list<uint64_t> &l,
                   uint64_t i) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      uint64_t i;
      const list<uint64_t> *l;
    };

    /// _Resume1: saves [i], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t i;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    list<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{i, &l});
    /// Loopified find_indices_aux: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t i = _f.i;
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{i});
            _stack.emplace_back(_Enter{(i + 1), a1.get()});
          } else {
            _stack.emplace_back(_Enter{(i + 1), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<uint64_t>::cons(_f.i, std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static list<uint64_t> find_indices(F0 &&p, const list<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }

  /// member x l checks if x is in the list.
  static bool member(uint64_t x, const list<uint64_t> &l);
  /// product l multiplies all elements in the list.
  static uint64_t product(const list<uint64_t> &l);
  /// sum_list l sums all elements in the list.
  static uint64_t sum_list(const list<uint64_t> &l);

  /// flatten l flattens a list of lists.
  template <typename T1>
  static list<T1>
  flatten(const list<list<T1>> &l) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const list<list<T1>> *l;
    };

    /// _Resume_Cons: saves [app, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      std::function<list<T1>(list<T1>, list<T1>)> app;
      list<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified flatten: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<list<T1>> &l = *_f.l;
        if (std::holds_alternative<typename list<list<T1>>::Nil>(l.v())) {
          _result = list<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<list<T1>>::Cons>(l.v());
          auto app_impl = [](auto &_self_app, const list<T1> &l1,
                             list<T1> l2) -> list<T1> {
            if (std::holds_alternative<typename list<T1>::Nil>(l1.v())) {
              return l2;
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<T1>::Cons>(l1.v());
              return list<T1>::cons(a00,
                                    _self_app(_self_app, *a10, std::move(l2)));
            }
          };
          auto app = [&](const list<T1> &l1, list<T1> l2) -> list<T1> {
            return app_impl(app_impl, l1, l2);
          };
          _stack.emplace_back(_Resume_Cons{std::move(app), a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.app)(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  /// flatten_nested l alternative flatten with different pattern: flattens one
  /// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
  /// :: flatten (xs :: rest).
  static list<uint64_t> flatten_nested_fuel(uint64_t fuel,
                                            const list<list<uint64_t>> &l);
  static uint64_t sum_list_lengths(const list<list<uint64_t>> &l);
  static list<uint64_t> flatten_nested(const list<list<uint64_t>> &l);
  /// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
  static list<uint64_t> compress(const list<uint64_t> &l);
  /// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
  /// (1,2),(3,4).
  static list<std::pair<uint64_t, uint64_t>>
  group_pairs(const list<uint64_t> &l);
  /// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
  static std::pair<list<uint64_t>, list<uint64_t>>
  swizzle(const list<uint64_t> &l);
  /// index_of_aux x l i finds first index of x in l starting from i.
  static uint64_t index_of_aux(uint64_t x, const list<uint64_t> &l, uint64_t i);
  static uint64_t index_of(uint64_t x, const list<uint64_t> &l);
  /// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
  static list<uint64_t> interleave(list<uint64_t> l1, list<uint64_t> l2);
  /// lookup key l finds value for key in association list.
  static uint64_t lookup(uint64_t key,
                         const list<std::pair<uint64_t, uint64_t>> &l);
  /// group l groups consecutive equal elements: 1,1,2,2,2,3 ->
  /// [1,1],[2,2,2],[3].
  static list<list<uint64_t>> group_fuel(uint64_t fuel,
                                         const list<uint64_t> &l);
  static list<list<uint64_t>> group(const list<uint64_t> &l);
  /// Internal helper: reverse a list.
  static list<uint64_t> rev_helper(list<uint64_t> acc, const list<uint64_t> &l);
  /// reverse_insert x l inserts x and reverses at each step.
  static list<uint64_t> reverse_insert(uint64_t x, const list<uint64_t> &l);
  /// Internal helper: append lists.
  static list<uint64_t> app_helper(const list<uint64_t> &l1, list<uint64_t> l2);
  /// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
  static list<uint64_t> double_append(const list<uint64_t> &l1,
                                      list<uint64_t> l2);
  /// remove_if_sum_even l removes element if sum with next is even.
  static list<uint64_t> remove_if_sum_even(const list<uint64_t> &l);
  /// split_at n l splits list at index n into (prefix, suffix).
  static std::pair<list<uint64_t>, list<uint64_t>> split_at(uint64_t n,
                                                            list<uint64_t> l);

  /// span p l splits list at first element not satisfying p.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<list<uint64_t>, list<uint64_t>>
  span(F0 &&p,
       list<uint64_t>
           l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      list<uint64_t> l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<list<uint64_t>, list<uint64_t>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l)});
    /// Loopified span: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<uint64_t> l = std::move(_f.l);
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v_mut())) {
          _result =
              std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
        } else {
          auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v_mut());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{*a1});
          } else {
            _result = std::make_pair(list<uint64_t>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        uint64_t a0 = _f.a0;
        auto _cs = std::move(_result);
        list<uint64_t> a = std::move(_cs.first);
        list<uint64_t> b = std::move(_cs.second);
        _result = std::make_pair(
            list<uint64_t>::cons(std::move(a0), std::move(a)), std::move(b));
      }
    }
    return _result;
  }

  /// unzip l splits list of pairs into two lists.
  static std::pair<list<uint64_t>, list<uint64_t>>
  unzip(const list<std::pair<uint64_t, uint64_t>> &l);
  /// nth n l default returns nth element or default if out of bounds.
  static uint64_t nth(uint64_t n, const list<uint64_t> &l, uint64_t default0);
  /// last l default returns last element or default if empty.
  static uint64_t last(const list<uint64_t> &l, uint64_t default0);
  /// drop n l drops first n elements.
  static list<uint64_t> drop(uint64_t n, list<uint64_t> l);
  /// init l returns all but last element.
  static list<uint64_t> init(const list<uint64_t> &l);
  /// count x l counts occurrences of x in l.
  static uint64_t count(uint64_t x, const list<uint64_t> &l);
  /// maximum l finds maximum element (returns 0 for empty list).
  static uint64_t maximum(const list<uint64_t> &l);
  /// minmax l finds both minimum and maximum in one pass.
  static std::pair<uint64_t, uint64_t> minmax(const list<uint64_t> &l);
  /// Helper for rotate_left.
  static list<uint64_t> rotate_left_fuel(uint64_t fuel, uint64_t n,
                                         list<uint64_t> l);
  /// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
  /// 3,4,1,2.
  static list<uint64_t> rotate_left(uint64_t n, const list<uint64_t> &l);
  /// intercalate sep lists joins lists with separator: intercalate 0
  /// [1,2],[3,4] -> 1,2,0,3,4.
  static list<uint64_t> intercalate(const list<uint64_t> &sep,
                                    const list<list<uint64_t>> &lists);
  /// majority l finds majority element using Boyer-Moore voting algorithm.
  /// Returns (candidate, count).
  static std::pair<uint64_t, uint64_t> majority(const list<uint64_t> &l);
  /// zip3 l1 l2 l3 zips three lists into triples.
  static list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
  zip3(const list<uint64_t> &l1, const list<uint64_t> &l2,
       const list<uint64_t> &l3);
  /// sum_and_count l returns both sum and count in one pass.
  static std::pair<uint64_t, uint64_t> sum_and_count(const list<uint64_t> &l);
  /// elem_at n l returns element at index n (like nth but with different name).
  static std::optional<uint64_t> elem_at(uint64_t n, const list<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LISTS
