#ifndef INCLUDED_MONADIC
#define INCLUDED_MONADIC

#include <any>
#include <functional>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }
};

struct Monadic {
  template <typename T1> static std::optional<T1> option_return(T1 x) {
    return std::make_optional<T1>(x);
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<std::optional<T2>, F1 &, T1 &>
  static std::optional<T2> option_bind(const std::optional<T1> &ma, F1 &&f) {
    if (ma.has_value()) {
      const T1 &a = *ma;
      return f(a);
    } else {
      return std::optional<T2>();
    }
  }

  static std::optional<uint64_t> safe_div(uint64_t n, uint64_t m);
  static std::optional<uint64_t> safe_sub(uint64_t n, uint64_t m);
  static std::optional<uint64_t> div_then_sub(uint64_t a, uint64_t b,
                                              uint64_t c);
  template <typename s, typename a>
  using State = std::function<std::pair<a, s>(s)>;

  template <typename T1, typename T2> static State<T1, T2> state_return(T2 x) {
    return [=](T1 s) mutable { return std::make_pair(x, s); };
  }

  template <typename T1, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<State<T1, T3>, F1 &, T2 &>
  static State<T1, T3> state_bind(State<T1, T2> ma, F1 &&f) {
    return [=](const T1 &s) mutable {
      auto [a, s_] = ma(s);
      return f(a)(s_);
    };
  }

  template <typename T1> static const State<T1, T1> &state_get() {
    static const State<T1, T1> v = [](const auto &s) {
      return std::make_pair(s, s);
    };
    return v;
  }

  template <typename T1> static State<T1, std::monostate> state_put(T1 s) {
    return
        [=](const T1 &) mutable { return std::make_pair(std::monostate{}, s); };
  }

  template <typename T1>
  static State<uint64_t, uint64_t> count_elements(const List<T1> &l) {
    return l.template fold_left<State<uint64_t, uint64_t>>(
        [](std::function<std::pair<uint64_t, uint64_t>(uint64_t)> acc,
           const T1 &) {
          return state_bind<uint64_t, uint64_t, uint64_t>(acc, [](uint64_t) {
            return state_bind<uint64_t, uint64_t, uint64_t>(
                state_get<uint64_t>(), [](uint64_t n) {
                  return state_bind<uint64_t, std::monostate, uint64_t>(
                      state_put<uint64_t>((n + 1)),
                      [=](std::monostate) mutable {
                        return state_return<uint64_t, uint64_t>(n);
                      });
                });
          });
        },
        state_return<uint64_t, uint64_t>(UINT64_C(0)));
  }

  static inline const std::optional<uint64_t> test_return =
      option_return<uint64_t>(UINT64_C(42));
  static inline const std::optional<uint64_t> test_bind_some =
      option_bind<uint64_t, uint64_t>(
          std::make_optional<uint64_t>(UINT64_C(10)), [](uint64_t x) {
            return std::make_optional<uint64_t>((x + UINT64_C(1)));
          });
  static inline const std::optional<uint64_t> test_bind_none =
      option_bind<uint64_t, uint64_t>(
          std::optional<uint64_t>(), [](uint64_t x) {
            return std::make_optional<uint64_t>((x + UINT64_C(1)));
          });
  static inline const std::optional<uint64_t> test_safe_div_ok =
      safe_div(UINT64_C(10), UINT64_C(3));
  static inline const std::optional<uint64_t> test_safe_div_zero =
      safe_div(UINT64_C(10), UINT64_C(0));
  static inline const std::optional<uint64_t> test_chain_ok =
      div_then_sub(UINT64_C(20), UINT64_C(4), UINT64_C(2));
  static inline const std::optional<uint64_t> test_chain_fail =
      div_then_sub(UINT64_C(20), UINT64_C(0), UINT64_C(2));
  static inline const std::pair<uint64_t, uint64_t> test_state =
      count_elements<uint64_t>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(
                      UINT64_C(4), List<uint64_t>::cons(
                                       UINT64_C(5), List<uint64_t>::nil()))))))(
          UINT64_C(0));
};

#endif // INCLUDED_MONADIC
