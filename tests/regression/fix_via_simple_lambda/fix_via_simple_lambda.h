#ifndef INCLUDED_FIX_VIA_SIMPLE_LAMBDA
#define INCLUDED_FIX_VIA_SIMPLE_LAMBDA

#include <functional>
#include <memory>
#include <optional>

struct FixViaSimpleLambda {
  /// Two local fixpoints both capture a let-binding base via &.
  /// They are combined in a simple lambda fun x => ... which captures
  /// them by = (since simple lambdas use value capture).
  ///
  /// BUG HYPOTHESIS: Copying a std::function that wraps a & lambda
  /// does NOT fix the dangling references. The = capture on the outer
  /// lambda copies the std::function objects, but the internal &
  /// closures still reference the destroyed stack variable base.
  ///
  /// This is a different escape mechanism from existing tests:
  /// the fixpoints don't escape directly through a constructor —
  /// they escape INDIRECTLY by being captured in a simple lambda
  /// that is then stored in Some.
  static std::optional<std::function<uint64_t(uint64_t)>>
  make_combined(uint64_t n);
  /// test1: base=42, double_add(5) = 42+10 = 52,
  /// triple_add(5) = 42+15 = 57. Total = 109.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_combined(UINT64_C(21));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test2: With intervening computation to clobber the stack.
  /// base=200, double_add(0) = 200, triple_add(0) = 200. Total = 400.
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
  /// test3: Larger recursion depth to increase chance of stack corruption.
  /// base=10, double_add(20) = 10+40 = 50,
  /// triple_add(20) = 10+60 = 70. Total = 120.
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
