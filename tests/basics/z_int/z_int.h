#ifndef INCLUDED_Z_INT
#define INCLUDED_Z_INT

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

struct ZIntTest {
  __attribute__((pure)) static int64_t add_test(const int64_t &_x0,
                                                const int64_t &_x1);
  __attribute__((pure)) static int64_t mul_test(const int64_t &_x0,
                                                const int64_t &_x1);
  __attribute__((pure)) static int64_t sub_test(const int64_t &_x0,
                                                const int64_t &_x1);
  __attribute__((pure)) static int64_t abs_test(const int64_t &_x0);
  __attribute__((pure)) static int64_t opp_test(const int64_t &_x0);
  __attribute__((pure)) static bool eqb_test(const int64_t &_x0,
                                             const int64_t &_x1);
  __attribute__((pure)) static bool ltb_test(const int64_t &_x0,
                                             const int64_t &_x1);
  __attribute__((pure)) static bool leb_test(const int64_t &_x0,
                                             const int64_t &_x1);
  static inline const int64_t zero_val = INT64_C(0);
  static inline const int64_t pos_val = INT64_C(42);
  static inline const int64_t neg_val = INT64_C(-7);
  static inline const int64_t big_val = INT64_C(1000);
  __attribute__((pure)) static int64_t z_sign(const int64_t &z);
};

#endif // INCLUDED_Z_INT
