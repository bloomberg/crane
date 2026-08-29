#ifndef INCLUDED_FIX_VIA_SIMPLE_LAMBDA
#define INCLUDED_FIX_VIA_SIMPLE_LAMBDA

#include <functional>
#include <memory>
#include <optional>

struct FixViaSimpleLambda {
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_combined(uint64_t n);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_combined(UINT64_C(21));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  static inline const uint64_t test2 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> opt =
        make_combined(UINT64_C(100));
    uint64_t noise =
        (((((((((UINT64_C(1) + UINT64_C(2)) + UINT64_C(3)) + UINT64_C(4)) +
              UINT64_C(5)) +
             UINT64_C(6)) +
            UINT64_C(7)) +
           UINT64_C(8)) +
          UINT64_C(9)) +
         UINT64_C(10));
    if (opt.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *opt;
      return f(UINT64_C(0));
    } else {
      return noise;
    }
  }();
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = make_combined(UINT64_C(5));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(20));
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_FIX_VIA_SIMPLE_LAMBDA
