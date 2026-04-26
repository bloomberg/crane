#ifndef INCLUDED_MODULO_WRAP
#define INCLUDED_MODULO_WRAP

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

struct Nat {
  __attribute__((pure)) static unsigned int pow(const unsigned int &n,
                                                const unsigned int &m);
};

struct ModuloWrap {
  __attribute__((pure)) static unsigned int
  addr12_of_nat(const unsigned int &n);
  static inline const unsigned int test_addr12_wrap =
      addr12_of_nat((Nat::pow(2u, 12u) + 5u));
  __attribute__((pure)) static unsigned int byte_of_nat(const unsigned int &n);
  static inline const unsigned int test_byte_wrap = byte_of_nat(263u);
  __attribute__((pure)) static unsigned int
  nibble_of_nat(const unsigned int &n);
  static inline const unsigned int test_nibble_wrap = nibble_of_nat(19u);
  static inline const std::pair<std::pair<unsigned int, unsigned int>,
                                unsigned int>
      t = std::make_pair(std::make_pair(test_addr12_wrap, test_byte_wrap),
                         test_nibble_wrap);
};

#endif // INCLUDED_MODULO_WRAP
