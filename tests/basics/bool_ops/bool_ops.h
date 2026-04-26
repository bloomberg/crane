#ifndef INCLUDED_BOOL_OPS
#define INCLUDED_BOOL_OPS

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

struct BoolOps {
  static inline const bool bool_true = true;
  static inline const bool bool_false = false;
  __attribute__((pure)) static bool my_negb(const bool &b);
  __attribute__((pure)) static bool my_andb(const bool &a, bool b);
  __attribute__((pure)) static bool my_orb(const bool &a, bool b);
  __attribute__((pure)) static bool my_xorb(const bool &a, const bool &b);
  __attribute__((pure)) static unsigned int
  if_nat(const bool &b, unsigned int t, unsigned int f);
  __attribute__((pure)) static bool complex_bool(const bool &a, const bool &b,
                                                 const bool &c);
  __attribute__((pure)) static bool nat_eq(const unsigned int &_x0,
                                           const unsigned int &_x1);
  __attribute__((pure)) static bool nat_lt(const unsigned int &_x0,
                                           const unsigned int &_x1);
  __attribute__((pure)) static bool nat_le(const unsigned int &_x0,
                                           const unsigned int &_x1);
  static inline const bool test_neg_t = my_negb(true);
  static inline const bool test_neg_f = my_negb(false);
  static inline const bool test_and_tt = my_andb(true, true);
  static inline const bool test_and_tf = my_andb(true, false);
  static inline const bool test_or_ff = my_orb(false, false);
  static inline const bool test_or_ft = my_orb(false, true);
  static inline const bool test_xor_tt = my_xorb(true, true);
  static inline const bool test_xor_tf = my_xorb(true, false);
  static inline const unsigned int test_if_t = if_nat(true, 5u, 3u);
  static inline const unsigned int test_if_f = if_nat(false, 5u, 3u);
  static inline const bool test_complex = complex_bool(true, false, true);
  static inline const bool test_eq_tt = nat_eq(5u, 5u);
  static inline const bool test_eq_tf = nat_eq(5u, 3u);
  static inline const bool test_lt = nat_lt(3u, 5u);
};

#endif // INCLUDED_BOOL_OPS
