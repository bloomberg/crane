#ifndef INCLUDED_ANON_FIXPOINT
#define INCLUDED_ANON_FIXPOINT

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct AnonFixpoint {
  __attribute__((pure)) static unsigned int sum_to(const unsigned int &n);
  __attribute__((pure)) static unsigned int factorial(const unsigned int &m);
  __attribute__((pure)) static unsigned int double_sum(const unsigned int &m);
  __attribute__((pure)) static unsigned int gcd(const unsigned int &a,
                                                const unsigned int &b);
  __attribute__((pure)) static unsigned int test_shadow(const unsigned int &n);
  static inline const unsigned int test_sum_5 = sum_to(5u);
  static inline const unsigned int test_sum_0 = sum_to(0u);
  static inline const unsigned int test_fact_5 = factorial(5u);
  static inline const unsigned int test_fact_0 = factorial(0u);
  static inline const unsigned int test_double = double_sum(3u);
  static inline const unsigned int test_gcd = gcd((4u * 3u), (2u * 3u));
};

#endif // INCLUDED_ANON_FIXPOINT
