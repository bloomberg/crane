#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Option {
  static inline const std::optional<unsigned int> some_val =
      std::make_optional<unsigned int>(5u);

  static inline const std::optional<unsigned int> none_val = std::nullopt;

  static unsigned int get_or_default(const std::optional<unsigned int> o,
                                     const unsigned int default0);

  static inline const std::optional<std::optional<unsigned int>> nested_some =
      std::make_optional<std::optional<unsigned int>>(
          std::make_optional<unsigned int>(3u));

  static inline const std::optional<std::optional<unsigned int>> nested_none =
      std::make_optional<std::optional<unsigned int>>(std::nullopt);

  static std::optional<unsigned int> safe_pred(const unsigned int n);

  static std::optional<unsigned int>
  chain_options(const std::optional<unsigned int> o1,
                const std::optional<unsigned int> o2);

  template <typename T1, typename T2>
  static std::optional<T2>
  apply_if_some(const std::optional<std::function<T2(T1)>> f, const T1 x) {
    if (f.has_value()) {
      std::function<T2(T1)> g = *f;
      return std::make_optional<T2>(g(x));
    } else {
      return std::nullopt;
    }
  }

  static inline const unsigned int test_some = get_or_default(some_val, 0u);

  static inline const unsigned int test_none = get_or_default(none_val, 0u);

  static inline const std::optional<unsigned int> test_pred_zero =
      safe_pred(0u);

  static inline const std::optional<unsigned int> test_pred_five =
      safe_pred(5u);
};
