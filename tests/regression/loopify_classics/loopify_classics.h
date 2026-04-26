#ifndef INCLUDED_LOOPIFY_CLASSICS
#define INCLUDED_LOOPIFY_CLASSICS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

struct LoopifyClassics {
  __attribute__((pure)) static unsigned int factorial(const unsigned int &n);
  __attribute__((pure)) static unsigned int fib(const unsigned int &n);
  __attribute__((pure)) static unsigned int ack_fuel(const unsigned int &fuel,
                                                     const unsigned int &m,
                                                     const unsigned int &n);
  __attribute__((pure)) static unsigned int ack(const unsigned int &m,
                                                const unsigned int &n);
  __attribute__((pure)) static unsigned int
  binomial_fuel(const unsigned int &fuel, const unsigned int &n,
                const unsigned int &k);
  __attribute__((pure)) static unsigned int binomial(const unsigned int &n,
                                                     const unsigned int &k);
  __attribute__((pure)) static unsigned int
  pascal_fuel(const unsigned int &fuel, const unsigned int &row,
              const unsigned int &col);
  __attribute__((pure)) static unsigned int pascal(const unsigned int &row,
                                                   const unsigned int &col);
  __attribute__((pure)) static unsigned int
  gcd_fuel(const unsigned int &fuel, unsigned int a, const unsigned int &b);
  __attribute__((pure)) static unsigned int gcd(const unsigned int &a,
                                                const unsigned int &b);
  __attribute__((pure)) static unsigned int power(const unsigned int &base,
                                                  const unsigned int &exp);
  __attribute__((pure)) static unsigned int sum_to(const unsigned int &n);
  __attribute__((pure)) static unsigned int sum_squares(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_CLASSICS
