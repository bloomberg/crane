#ifndef INCLUDED_Z_ABS_MIN
#define INCLUDED_Z_ABS_MIN

#include <cstdint>
#include <cstdlib>
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

struct ZAbsMin {
  /// In Rocq, Z.abs is total: Z.abs z is always non-negative.
  /// ZInt maps Z.abs to std::abs(%a0) (from <cstdlib>).
  /// But std::abs(INT64_MIN) is undefined behavior in C++
  /// because -INT64_MIN cannot be represented as int64_t.
  __attribute__((pure)) static int64_t my_abs(const int64_t &_x0);
  /// Construct INT64_MIN = -2^63 via INT64_MAX + 1 negated.
  static inline const int64_t neg_max = (-INT64_C(9223372036854775807));
  static inline const int64_t int64_min = (neg_max - 1);
  /// In Rocq, this is 9223372036854775808 (positive).
  /// In C++, std::abs(INT64_MIN) is UB — typically returns INT64_MIN.
  static inline const int64_t abs_of_min = std::abs(int64_min);
  /// Should always be true for Z.abs, but fails in C++.
  __attribute__((pure)) static bool is_nonneg(const int64_t &x);
};

#endif // INCLUDED_Z_ABS_MIN
