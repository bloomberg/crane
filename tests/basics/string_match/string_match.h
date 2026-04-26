#ifndef INCLUDED_STRING_MATCH
#define INCLUDED_STRING_MATCH

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>

using namespace std::string_literals;
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

struct StringMatch {
  static inline const std::string str_empty = "";
  static inline const std::string str_hello = "hello";
  static inline const std::string str_world = "world";
  static inline const std::string str_cat = "hello "s + "world"s;
  static inline const int64_t str_len_empty = ""s.length();
  static inline const int64_t str_len_hello = "hello"s.length();
  __attribute__((pure)) static bool is_empty(const std::string s);
  static inline const bool test_empty_true = is_empty("");
  static inline const bool test_empty_false = is_empty("x");
  static inline const std::string test_cat = "foo"s + "bar"s;
};

#endif // INCLUDED_STRING_MATCH
