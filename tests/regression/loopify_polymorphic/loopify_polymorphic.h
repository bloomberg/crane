#ifndef INCLUDED_LOOPIFY_POLYMORPHIC
#define INCLUDED_LOOPIFY_POLYMORPHIC

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
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
                return A{[&]() -> typename A::first_type {
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
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
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

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct LoopifyPolymorphic {
  template <typename T1>
  static uint64_t
  poly_length(const List<T1> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(UINT64_C(1))> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{UINT64_C(1)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f._s0 + std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1>
  poly_reverse(const List<T1> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(List<T1>::cons(std::declval<T1 &>(),
                                           List<T1>::nil()))>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_reverse: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(
              _Resume_Cons{List<T1>::cons(a0, List<T1>::nil())});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_result).app(_f._s0);
      }
    }
    return _result;
  }

  template <typename T1>
  static List<T1>
  poly_append(const List<T1> &l1,
              List<T1> l2) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      List<T1> l2;
      const List<T1> *l1;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l2), &l1});
    /// Loopified poly_append: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<T1> l2 = std::move(_f.l2);
        const List<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          _result = std::move(l2);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l1.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{std::move(l2), a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<T1>::cons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1> static std::optional<T1> poly_last(const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  template <typename T1>
  static List<T1>
  poly_take(uint64_t n,
            const List<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const List<T1> *l;
      uint64_t n;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, n});
    /// Loopified poly_take: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = List<T1>::nil();
        } else {
          uint64_t n_ = n - 1;
          if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
            _result = List<T1>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
            _stack.emplace_back(_Resume_Cons{a0});
            _stack.emplace_back(_Enter{a1.get(), n_});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<T1>::cons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1> static List<T1> poly_drop(uint64_t n, List<T1> l) {
    List<T1> _loop_l = std::move(l);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        return _loop_l;
      } else {
        uint64_t n_ = _loop_n - 1;
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l.v_mut())) {
          return List<T1>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l.v_mut());
          _loop_l = *a1;
          _loop_n = n_;
        }
      }
    }
  }

  template <typename T1>
  static std::optional<T1> poly_nth(uint64_t n, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return std::optional<T1>();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (_loop_n == UINT64_C(0)) {
          return std::make_optional<T1>(a0);
        } else {
          _loop_l = a1.get();
          _loop_n = ((
              (_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
        }
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static List<T1>
  poly_filter(F0 &&p,
              const List<T1> &l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      std::decay_t<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_filter: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<T1>::cons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static List<T2>
  poly_map(F0 &&f,
           const List<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<T2> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified poly_map: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = List<T2>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<T2>::cons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static List<std::pair<T1, T2>>
  poly_zip(const List<T1> &l1,
           const List<T2> &l2) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const List<T2> *l2;
      const List<T1> *l1;
    };

    /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(std::make_pair(std::declval<T1 &>(),
                                           std::declval<T2 &>()))>
          _s0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<std::pair<T1, T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l2, &l1});
    /// Loopified poly_zip: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T2> &l2 = *_f.l2;
        const List<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename List<T1>::Nil>(l1.v())) {
          _result = List<std::pair<T1, T2>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l1.v());
          if (std::holds_alternative<typename List<T2>::Nil>(l2.v())) {
            _result = List<std::pair<T1, T2>>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename List<T2>::Cons>(l2.v());
            _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a00)});
            _stack.emplace_back(_Enter{a10.get(), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = List<std::pair<T1, T2>>::cons(_f._s0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2>
  static std::pair<List<T1>, List<T2>>
  poly_unzip(const List<std::pair<T1, T2>> &l) {
    if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(l.v())) {
      return std::make_pair(List<T1>::nil(), List<T2>::nil());
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, T2>>::Cons>(l.v());
      const auto &[a, b] = a0;
      auto [as_, bs] = poly_unzip<T1, T2>(*a1);
      return std::make_pair(List<T1>::cons(a, std::move(as_)),
                            List<T2>::cons(b, std::move(bs)));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::pair<List<T1>, List<T1>> poly_partition(F0 &&p,
                                                      const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto [trues, falses] = poly_partition<T1>(p, *a1);
      if (p(a0)) {
        return std::make_pair(List<T1>::cons(a0, std::move(trues)),
                              std::move(falses));
      } else {
        return std::make_pair(std::move(trues),
                              List<T1>::cons(a0, std::move(falses)));
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool poly_member(F0 &&eq, const T1 &x, const List<T1> &l) {
    const List<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<T1>::Nil>(_loop_l->v())) {
        return false;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          return true;
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  template <typename T1>
  static List<T1> poly_replicate(
      uint64_t n,
      T1 x) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      uint64_t n;
    };

    /// _Resume_n_: resumes after recursive call with _result.
    struct _Resume_n_ {};

    using _Frame = std::variant<_Enter, _Resume_n_>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{n});
    /// Loopified poly_replicate: _Enter -> _Resume_n_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = List<T1>::nil();
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(_Resume_n_{});
          _stack.emplace_back(_Enter{n_});
        }
      } else {
        auto _f = std::move(std::get<_Resume_n_>(_frame));
        _result = List<T1>::cons(x, std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t nat_length(const List<uint64_t> &_x0);
  static List<uint64_t> nat_reverse(const List<uint64_t> &_x0);
  static List<uint64_t> nat_append(const List<uint64_t> &_x0,
                                   const List<uint64_t> &_x1);
  static std::optional<uint64_t> nat_last(const List<uint64_t> &_x0);
  static List<uint64_t> nat_take(uint64_t _x0, const List<uint64_t> &_x1);
  static List<uint64_t> nat_drop(uint64_t _x0, const List<uint64_t> &_x1);
  static std::optional<uint64_t> nat_nth(uint64_t _x0,
                                         const List<uint64_t> &_x1);
  static bool nat_eq(uint64_t _x0, uint64_t _x1);
  static bool is_even(uint64_t x);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> nat_filter(F0 &&_x0, const List<uint64_t> &_x1) {
    return poly_filter<uint64_t>(_x0, _x1);
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t> nat_map(F0 &&_x0, const List<uint64_t> &_x1) {
    return poly_map<uint64_t, uint64_t>(_x0, _x1);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::pair<List<uint64_t>, List<uint64_t>>
  nat_partition(F0 &&_x0, const List<uint64_t> &_x1) {
    return poly_partition<uint64_t>(_x0, _x1);
  }

  static bool nat_member(uint64_t _x0, const List<uint64_t> &_x1);
  static List<uint64_t> nat_replicate(uint64_t _x0, uint64_t _x1);
};

#endif // INCLUDED_LOOPIFY_POLYMORPHIC
