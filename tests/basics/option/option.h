#ifndef INCLUDED_OPTION
#define INCLUDED_OPTION

#include <functional>
#include <memory>
#include <optional>

struct Option {
  static inline const std::optional<uint64_t> some_val =
      std::make_optional<uint64_t>(UINT64_C(5));
  static inline const std::optional<uint64_t> none_val =
      std::optional<uint64_t>();
  static uint64_t get_or_default(const std::optional<uint64_t> &o,
                                 uint64_t default0);
  static inline const std::optional<std::optional<uint64_t>> nested_some =
      std::make_optional<std::optional<uint64_t>>(
          std::make_optional<uint64_t>(UINT64_C(3)));
  static inline const std::optional<std::optional<uint64_t>> nested_none =
      std::make_optional<std::optional<uint64_t>>(std::optional<uint64_t>());
  static std::optional<uint64_t> safe_pred(uint64_t n);
  static std::optional<uint64_t> chain_options(std::optional<uint64_t> o1,
                                               std::optional<uint64_t> o2);

  template <typename T1, typename T2>
  static std::optional<T2>
  apply_if_some(const std::optional<std::function<T2(T1)>> &f, const T1 &x) {
    if (f.has_value()) {
      const std::function<T2(T1)> &g = *f;
      return std::make_optional<T2>(g(x));
    } else {
      return std::optional<T2>();
    }
  }

  static inline const uint64_t test_some =
      Option::get_or_default(Option::some_val, UINT64_C(0));
  static inline const uint64_t test_none =
      Option::get_or_default(Option::none_val, UINT64_C(0));
  static inline const std::optional<uint64_t> test_pred_zero =
      Option::safe_pred(UINT64_C(0));
  static inline const std::optional<uint64_t> test_pred_five =
      Option::safe_pred(UINT64_C(5));
};

#endif // INCLUDED_OPTION
