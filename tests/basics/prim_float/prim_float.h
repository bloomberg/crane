#ifndef INCLUDED_PRIM_FLOAT
#define INCLUDED_PRIM_FLOAT

#include <cmath>
#include <cstdint>
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

struct PrimFloat {
  static inline const double f_zero = 0x0p+0;
  static inline const double f_one = 0x1p+0;
  static inline const double f_neg_one = (-0x1p+0);
  __attribute__((pure)) static double test_add(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_sub(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_mul(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_div(const double _x0,
                                               const double _x1);
  __attribute__((pure)) static double test_opp(const double _x0);
  __attribute__((pure)) static double test_abs(const double _x0);
  __attribute__((pure)) static double test_sqrt(const double _x0);
  __attribute__((pure)) static bool test_eqb(const double _x0,
                                             const double _x1);
  __attribute__((pure)) static bool test_ltb(const double _x0,
                                             const double _x1);
  __attribute__((pure)) static bool test_leb(const double _x0,
                                             const double _x1);
  __attribute__((pure)) static double test_of_uint63(const int64_t _x0);
};

#endif // INCLUDED_PRIM_FLOAT
