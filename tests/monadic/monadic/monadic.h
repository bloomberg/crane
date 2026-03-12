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

enum class unit { tt };

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, MapsTo<T1, T1, A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{[&](const typename List<A>::nil _args) -> T1 { return a0; },
                   [&](const typename List<A>::cons _args) -> T1 {
                     A b = _args._a0;
                     std::shared_ptr<List<A>> l0 = _args._a1;
                     return std::move(l0)->template fold_left<T1>(f, f(a0, b));
                   }},
        this->v());
  }
};

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);
  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct Monadic {
  template <typename T1> static std::optional<T1> option_return(const T1 x) {
    return std::make_optional<T1>(x);
  }

  template <typename T1, typename T2, MapsTo<std::optional<T2>, T1> F1>
  static std::optional<T2> option_bind(const std::optional<T1> ma, F1 &&f) {
    if (ma.has_value()) {
      T1 a = *ma;
      return f(a);
    } else {
      return std::nullopt;
    }
  }

  static std::optional<unsigned int> safe_div(const unsigned int n,
                                              const unsigned int m);
  static std::optional<unsigned int> safe_sub(const unsigned int n,
                                              const unsigned int m);
  static std::optional<unsigned int> div_then_sub(const unsigned int a,
                                                  const unsigned int b,
                                                  const unsigned int c);
  template <typename s, typename a>
  using State = std::function<std::pair<a, s>(s)>;

  template <typename T1, typename T2>
  static State<T1, T2> state_return(const T2 x) {
    return [=](T1 s) mutable { return std::make_pair(x, s); };
  }

  template <typename T1, typename T2, typename T3, MapsTo<State<T1, T3>, T2> F1>
  static State<T1, T3> state_bind(const State<T1, T2> ma, F1 &&f) {
    return [=](T1 s) mutable {
      T2 a = ma(s).first;
      T1 s_ = ma(s).second;
      return f(a)(s_);
    };
  }

  template <typename T1> static const State<T1, T1> &state_get() {
    static const State<T1, T1> v = [](T1 s) { return std::make_pair(s, s); };
    return v;
  }

  template <typename T1> static State<T1, unit> state_put(const T1 s) {
    return [=](T1 _x) mutable { return std::make_pair(unit::tt, s); };
  }

  template <typename T1>
  static State<unsigned int, unsigned int>
  count_elements(const std::shared_ptr<List<T1>> &l) {
    return l->template fold_left<State<unsigned int, unsigned int>>(
        [](std::function<std::pair<unsigned int, unsigned int>(unsigned int)>
               acc,
           T1 _x) {
          return state_bind<unsigned int, unsigned int, unsigned int>(
              acc, [](unsigned int _x0) {
                return state_bind<unsigned int, unsigned int, unsigned int>(
                    state_get<unsigned int>(), [](unsigned int n) {
                      return state_bind<unsigned int, unit, unsigned int>(
                          state_put<unsigned int>((n + 1)),
                          [=](unit _x1) mutable {
                            return state_return<unsigned int, unsigned int>(n);
                          });
                    });
              });
        },
        state_return<unsigned int, unsigned int>(0u));
  }

  static inline const std::optional<unsigned int> test_return =
      option_return<unsigned int>(42u);
  static inline const std::optional<unsigned int> test_bind_some =
      option_bind<unsigned int, unsigned int>(
          std::make_optional<unsigned int>(10u), [](unsigned int x) {
            return std::make_optional<unsigned int>((x + 1u));
          });
  static inline const std::optional<unsigned int> test_bind_none =
      option_bind<unsigned int, unsigned int>(std::nullopt, [](unsigned int x) {
        return std::make_optional<unsigned int>((x + 1u));
      });
  static inline const std::optional<unsigned int> test_safe_div_ok =
      safe_div(10u, 3u);
  static inline const std::optional<unsigned int> test_safe_div_zero =
      safe_div(10u, 0u);
  static inline const std::optional<unsigned int> test_chain_ok =
      div_then_sub(20u, 4u, 2u);
  static inline const std::optional<unsigned int> test_chain_fail =
      div_then_sub(20u, 0u, 2u);
  static inline const std::pair<unsigned int, unsigned int> test_state =
      count_elements<unsigned int>(List<unsigned int>::ctor::cons_(
          1u,
          List<unsigned int>::ctor::cons_(
              2u,
              List<unsigned int>::ctor::cons_(
                  3u, List<unsigned int>::ctor::cons_(
                          4u, List<unsigned int>::ctor::cons_(
                                  5u, List<unsigned int>::ctor::nil_()))))))(
          0u);
};
