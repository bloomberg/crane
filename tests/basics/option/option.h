#ifndef INCLUDED_OPTION
#define INCLUDED_OPTION

#include <functional>
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

struct Option {
  static inline const std::optional<unsigned int> some_val =
      std::make_optional<unsigned int>(5u);
  static inline const std::optional<unsigned int> none_val =
      std::optional<unsigned int>();
  __attribute__((pure)) static unsigned int
  get_or_default(const std::optional<unsigned int> &o, unsigned int default0);
  static inline const std::optional<std::optional<unsigned int>> nested_some =
      std::make_optional<std::optional<unsigned int>>(
          std::make_optional<unsigned int>(3u));
  static inline const std::optional<std::optional<unsigned int>> nested_none =
      std::make_optional<std::optional<unsigned int>>(
          std::optional<unsigned int>());
  __attribute__((pure)) static std::optional<unsigned int>
  safe_pred(const unsigned int &n);
  __attribute__((pure)) static std::optional<unsigned int>
  chain_options(std::optional<unsigned int> o1, std::optional<unsigned int> o2);

  template <typename T1, typename T2>
  __attribute__((pure)) static std::optional<T2>
  apply_if_some(const std::optional<std::function<T2(T1)>> &f, const T1 x) {
    if (f.has_value()) {
      const std::function<T2(T1)> &g = *f;
      return std::make_optional<T2>(g(x));
    } else {
      return std::optional<T2>();
    }
  }

  static inline const unsigned int test_some =
      Option::get_or_default(Option::some_val, 0u);
  static inline const unsigned int test_none =
      Option::get_or_default(Option::none_val, 0u);
  static inline const std::optional<unsigned int> test_pred_zero =
      Option::safe_pred(0u);
  static inline const std::optional<unsigned int> test_pred_five =
      Option::safe_pred(5u);
};

#endif // INCLUDED_OPTION
