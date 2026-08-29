#ifndef INCLUDED_FIX_HIGHER_ORDER
#define INCLUDED_FIX_HIGHER_ORDER

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

struct FixHigherOrder {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static std::optional<std::function<uint64_t(uint64_t)>> wrap_fn(F0 &&f) {
    return std::make_optional<std::function<uint64_t(uint64_t)>>(f);
  }

  static std::optional<std::function<uint64_t(uint64_t)>>
  make_wrapped(uint64_t base);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_wrapped(UINT64_C(5));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(999);
    }
  }();
  static inline const uint64_t test2 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> o =
        make_wrapped(UINT64_C(42));
    uint64_t noise =
        ((((UINT64_C(1) + UINT64_C(2)) + UINT64_C(3)) + UINT64_C(4)) +
         UINT64_C(5));
    if (o.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *o;
      return (f(UINT64_C(10)) + noise);
    } else {
      return UINT64_C(999);
    }
  }();

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static std::optional<std::optional<std::function<uint64_t(uint64_t)>>>
  double_wrap(F0 &&f) {
    return std::make_optional<std::optional<std::function<uint64_t(uint64_t)>>>(
        std::make_optional<std::function<uint64_t(uint64_t)>>(f));
  }

  static std::optional<std::optional<std::function<uint64_t(uint64_t)>>>
  make_double_wrapped(uint64_t base);
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = make_double_wrapped(UINT64_C(100));
    if (_cs.has_value()) {
      const std::optional<std::function<uint64_t(uint64_t)>> &o = *_cs;
      if (o.has_value()) {
        const std::function<uint64_t(uint64_t)> &f = *o;
        return f(UINT64_C(7));
      } else {
        return UINT64_C(999);
      }
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_FIX_HIGHER_ORDER
