#ifndef INCLUDED_INT63_ARITH
#define INCLUDED_INT63_ARITH

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

struct Int63Arith {
  static inline const int64_t i_zero = int64_t(0);
  static inline const int64_t i_one = int64_t(1);
  static inline const int64_t i_add =
      ((int64_t(10) + int64_t(20)) & 0x7FFFFFFFFFFFFFFFLL);
  static inline const int64_t i_mul =
      ((int64_t(6) * int64_t(7)) & 0x7FFFFFFFFFFFFFFFLL);
  static inline const int64_t i_sub =
      ((int64_t(50) - int64_t(8)) & 0x7FFFFFFFFFFFFFFFLL);
  static inline const bool i_eqb_true = int64_t(42) == int64_t(42);
  static inline const bool i_eqb_false = int64_t(42) == int64_t(43);
  static inline const bool i_ltb_true = int64_t(3) < int64_t(5);
  static inline const bool i_ltb_false = int64_t(5) < int64_t(3);
  static inline const bool i_leb_true = int64_t(3) <= int64_t(3);
  static inline const bool i_leb_false = int64_t(5) <= int64_t(3);
  __attribute__((pure)) static int64_t i_abs(const int64_t x);
  static inline const int64_t test_abs_pos = i_abs(int64_t(42));
  static inline const int64_t test_abs_neg =
      i_abs(((int64_t(0) - int64_t(42)) & 0x7FFFFFFFFFFFFFFFLL));
};

#endif // INCLUDED_INT63_ARITH
