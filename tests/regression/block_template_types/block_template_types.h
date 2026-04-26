#ifndef INCLUDED_BLOCK_TEMPLATE_TYPES
#define INCLUDED_BLOCK_TEMPLATE_TYPES

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
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

struct BlockTemplateTypes {
  /// %result inferred as unsigned int.
  static unsigned int test_read_nat();
  /// %result inferred as bool, with unsigned int in same scope.
  static std::string test_is_positive();
  /// %result inferred as unsigned int from string argument.
  /// Tests %a0 and %result together with nat return type.
  static unsigned int test_parse_nat();
  /// Three different block template types in one function:
  /// std::string (get_line), unsigned int (read_nat), bool (is_positive).
  static std::string test_mixed();
  /// Two unsigned int block templates with arithmetic on results.
  static unsigned int test_nat_arith();
};

#endif // INCLUDED_BLOCK_TEMPLATE_TYPES
