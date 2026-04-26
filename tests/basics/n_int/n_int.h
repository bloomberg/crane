#ifndef INCLUDED_N_INT
#define INCLUDED_N_INT

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

struct Pos {
  __attribute__((pure)) static unsigned int add_carry(const unsigned int &x,
                                                      const unsigned int &y);
};

struct NIntTest {
  __attribute__((pure)) static unsigned int add_test(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  __attribute__((pure)) static unsigned int mul_test(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  __attribute__((pure)) static unsigned int sub_test(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  __attribute__((pure)) static unsigned int div_test(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  __attribute__((pure)) static bool eqb_test(const unsigned int &_x0,
                                             const unsigned int &_x1);
  __attribute__((pure)) static bool ltb_test(const unsigned int &_x0,
                                             const unsigned int &_x1);
  __attribute__((pure)) static bool leb_test(const unsigned int &_x0,
                                             const unsigned int &_x1);
  __attribute__((pure)) static unsigned int succ_test(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int pred_test(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int
  double_test(const unsigned int &_x0);
  static inline const unsigned int zero_val = 0u;
  static inline const unsigned int five_val = 5u;
  static inline const unsigned int big_val = 1000u;
  __attribute__((pure)) static bool is_zero(const unsigned int &n);
  __attribute__((pure)) static unsigned int pos_add(const unsigned int &_x0,
                                                    const unsigned int &_x1);
  __attribute__((pure)) static unsigned int pos_succ(const unsigned int &_x0);
};

#endif // INCLUDED_N_INT
