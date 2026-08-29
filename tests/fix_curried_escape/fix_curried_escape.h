#ifndef INCLUDED_FIX_CURRIED_ESCAPE
#define INCLUDED_FIX_CURRIED_ESCAPE

#include <functional>
#include <memory>
#include <optional>

struct FixCurriedEscape {
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_fn(uint64_t base);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_fn(UINT64_C(42));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(999);
    }
  }();
  static inline const uint64_t test2 = []() -> uint64_t {
    auto _cs = make_fn(UINT64_C(10));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(7));
    } else {
      return UINT64_C(999);
    }
  }();
  static inline const uint64_t test3 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> fn1 =
        make_fn(UINT64_C(100));
    if (fn1.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *fn1;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_FIX_CURRIED_ESCAPE
