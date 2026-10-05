#ifndef INCLUDED_BRANCH_FACTS
#define INCLUDED_BRANCH_FACTS

#include <cstdint>
#include <utility>

/// Guards a declared operation's mapping keeps, dropped where the
/// enclosing branch, or a nonzero divisor, rules their case out -- and kept
/// where it does not.
struct BranchFacts {
  /// Unguarded in both branches: each knows which operand is larger.
  static uint64_t abs_diff(uint64_t a, uint64_t b);
  /// Unguarded: n is not zero in the else branch.
  static uint64_t pred_or_zero(uint64_t n);
  /// Guarded still: the branch knows a <= b, the wrong way round.
  static uint64_t wrong_way(uint64_t a, uint64_t b);
  /// Unguarded: the divisor is a nonzero numeral.
  static uint64_t half(uint64_t n);
  static uint64_t parity(uint64_t n);
  /// Guarded still: the divisor may be zero.
  static uint64_t ratio(uint64_t x0_, uint64_t x1_);
  static uint64_t rem(uint64_t x0_, uint64_t x1_);
  /// A match on bool returning its own truth value.
  static bool is_small(uint64_t n);
};

#endif // INCLUDED_BRANCH_FACTS
