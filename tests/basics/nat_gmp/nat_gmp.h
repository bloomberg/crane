#ifndef INCLUDED_NAT_GMP
#define INCLUDED_NAT_GMP

#include <gmpxx.h>
#include <memory>
#include <optional>
#include <type_traits>

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

struct NatGMPTest {
  __attribute__((pure)) static mpz_class add_test(const mpz_class &_x0,
                                                  const mpz_class &_x1);
  __attribute__((pure)) static mpz_class mul_test(const mpz_class &_x0,
                                                  const mpz_class &_x1);
  __attribute__((pure)) static mpz_class sub_test(const mpz_class &_x0,
                                                  const mpz_class &_x1);
  __attribute__((pure)) static bool eqb_test(const mpz_class &_x0,
                                             const mpz_class &_x1);
  __attribute__((pure)) static bool ltb_test(const mpz_class &_x0,
                                             const mpz_class &_x1);
  __attribute__((pure)) static bool leb_test(const mpz_class &_x0,
                                             const mpz_class &_x1);
  __attribute__((pure)) static mpz_class pred_test(const mpz_class &_x0);
  __attribute__((pure)) static mpz_class match_test(const mpz_class &n);
  static inline const mpz_class big_num = mpz_class(200);
  static inline const mpz_class another_big = mpz_class(1000);
  __attribute__((pure)) static mpz_class add_big(const mpz_class &n);
};

#endif // INCLUDED_NAT_GMP
