#ifndef INCLUDED_FIX_VIA_SIMPLE_LAMBDA
#define INCLUDED_FIX_VIA_SIMPLE_LAMBDA

#include "fn.h"
#include <cstdint>
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
  static std::optional<crane::fn<uint64_t(uint64_t)>> make_combined(uint64_t n);
  /// test1: base=42, double_add(5) = 42+10 = 52,
  /// triple_add(5) = 42+15 = 57. Total = 109.
  static constexpr uint64_t test1 = UINT64_C(109);
  /// test2: With intervening computation to clobber the stack.
  /// base=200, double_add(0) = 200, triple_add(0) = 200. Total = 400.
  static constexpr uint64_t test2 = UINT64_C(400);
  /// test3: Larger recursion depth to increase chance of stack corruption.
  /// base=10, double_add(20) = 10+40 = 50,
  /// triple_add(20) = 10+60 = 70. Total = 120.
  static constexpr uint64_t test3 = UINT64_C(120);
};

#endif // INCLUDED_FIX_VIA_SIMPLE_LAMBDA
