#ifndef INCLUDED_Z_DIV_MIN
#define INCLUDED_Z_DIV_MIN

#include <cstdint>
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

struct ZDivMin {
  /// Build INT64_MIN = -9223372036854775808 via Z.opp(Z.of_nat ...)
  static inline const int64_t neg_max = (-INT64_C(9223372036854775807));
  static inline const int64_t int64_min = (neg_max - 1);
  /// INT64_MIN / -1 = 9223372036854775808, which doesn't fit in int64_t.
  /// In Rocq: perfectly fine, result is positive.
  /// In C++: signed division overflow → undefined behavior.
  static inline const int64_t div_min_neg1 =
      (INT64_C(-1) == 0 ? INT64_C(0) : int64_min / INT64_C(-1));
  /// The result should be positive (dividing negative by negative).
  static inline const bool div_is_positive = INT64_C(0) < div_min_neg1;
  /// INT64_MIN % -1 = 0 in Rocq.
  /// In C++: also UB (same overflow issue).
  static inline const int64_t mod_min_neg1 =
      (INT64_C(-1) == 0 ? INT64_C(0) : int64_min % INT64_C(-1));
  /// Z.opp INT64_MIN is also UB: -(INT64_MIN) overflows int64_t.
  /// In Rocq: result is positive 9223372036854775808.
  static inline const int64_t opp_min = (-int64_min);
  static inline const bool opp_is_positive = INT64_C(0) < opp_min;
};

#endif // INCLUDED_Z_DIV_MIN
