#ifndef INCLUDED_CLOSURE_LET_ESCAPE
#define INCLUDED_CLOSURE_LET_ESCAPE

#include <functional>
#include <memory>
#include <optional>

struct ClosureLetEscape {
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_fn_fix(uint64_t n);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_fn_fix(UINT64_C(21));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(3));
    } else {
      return UINT64_C(999);
    }
  }();
  static inline const uint64_t test2 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> opt =
        make_fn_fix(UINT64_C(50));
    uint64_t noise =
        ((((UINT64_C(1) + UINT64_C(2)) + UINT64_C(3)) + UINT64_C(4)) +
         UINT64_C(5));
    if (opt.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *opt;
      return f(noise);
    } else {
      return UINT64_C(999);
    }
  }();
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_fn_multi(uint64_t n);

  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = make_fn_multi(UINT64_C(10));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_CLOSURE_LET_ESCAPE
