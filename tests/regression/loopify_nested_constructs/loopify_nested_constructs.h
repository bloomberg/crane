#ifndef INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
#define INCLUDED_LOOPIFY_NESTED_CONSTRUCTS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

struct LoopifyNestedConstructs {
  __attribute__((pure)) static unsigned int multi_let(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  nested_if_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int nested_if(const unsigned int &n);
  __attribute__((pure)) static unsigned int deep_nest(const unsigned int &n);
  __attribute__((pure)) static unsigned int let_nested(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  mod_pattern_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int mod_pattern(const unsigned int &n);
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  tuple_constr(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  alternating_ops(const unsigned int &n);
  __attribute__((pure)) static bool chained_comp_fuel(const unsigned int &fuel,
                                                      const unsigned int &n);
  __attribute__((pure)) static unsigned int chained_comp(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  compute_with_lets(const unsigned int &n);
  __attribute__((pure)) static unsigned int nested_match(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
