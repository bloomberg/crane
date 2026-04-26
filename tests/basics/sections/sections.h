#ifndef INCLUDED_SECTIONS
#define INCLUDED_SECTIONS

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

struct Sections {
  __attribute__((pure)) static unsigned int add_n(const unsigned int &_x0,
                                                  const unsigned int &_x1);
  __attribute__((pure)) static unsigned int mul_n(const unsigned int &_x0,
                                                  const unsigned int &_x1);
  __attribute__((pure)) static unsigned int add_five(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int mul_three(const unsigned int &_x0);
  __attribute__((pure)) static unsigned int sum_ab(const unsigned int &_x0,
                                                   const unsigned int &_x1);
  __attribute__((pure)) static unsigned int prod_ab(const unsigned int &_x0,
                                                    const unsigned int &_x1);
  __attribute__((pure)) static unsigned int use_inner(const unsigned int &a);
  static inline const unsigned int final_use = use_inner(5u);

  template <typename T1> static T1 identity(const T1 x) { return x; }

  template <typename T1> static T1 const_(const T1 x, const T1) { return x; }

  static inline const unsigned int test_add = add_five(2u);
  static inline const unsigned int test_mul = mul_three(4u);
  static inline const unsigned int test_nested = final_use;
  static inline const unsigned int test_id = identity<unsigned int>(7u);
  static inline const unsigned int test_const = const_<unsigned int>(3u, 9u);
};

#endif // INCLUDED_SECTIONS
