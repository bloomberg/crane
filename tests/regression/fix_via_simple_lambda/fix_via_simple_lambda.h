#ifndef INCLUDED_FIX_VIA_SIMPLE_LAMBDA
#define INCLUDED_FIX_VIA_SIMPLE_LAMBDA

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
  static std::optional<std::function<unsigned int(unsigned int)>>
  make_combined(const unsigned int &n);
  /// test1: base=42, double_add(5) = 42+10 = 52,
  /// triple_add(5) = 42+15 = 57. Total = 109.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_combined(21u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// test2: With intervening computation to clobber the stack.
  /// base=200, double_add(0) = 200, triple_add(0) = 200. Total = 400.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> opt =
        make_combined(100u);
    unsigned int noise =
        (((((((((1u + 2u) + 3u) + 4u) + 5u) + 6u) + 7u) + 8u) + 9u) + 10u);
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(0u);
    } else {
      return noise;
    }
  }();
  /// test3: Larger recursion depth to increase chance of stack corruption.
  /// base=10, double_add(20) = 10+40 = 50,
  /// triple_add(20) = 10+60 = 70. Total = 120.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_combined(5u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(20u);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_FIX_VIA_SIMPLE_LAMBDA
