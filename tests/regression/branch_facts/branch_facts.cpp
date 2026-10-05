#include "branch_facts.h"

/// Guards a declared operation's mapping keeps, dropped where the
/// enclosing branch, or a nonzero divisor, rules their case out -- and kept
/// where it does not.
/// Unguarded in both branches: each knows which operand is larger.
uint64_t BranchFacts::abs_diff(uint64_t a, uint64_t b) {
  if (b <= a) {
    return (a - b);
  } else {
    return (b - a);
  }
}

/// Unguarded: n is not zero in the else branch.
uint64_t BranchFacts::pred_or_zero(uint64_t n) {
  if (n == UINT64_C(0)) {
    return UINT64_C(0);
  } else {
    return (n - UINT64_C(1));
  }
}

/// Guarded still: the branch knows a <= b, the wrong way round.
uint64_t BranchFacts::wrong_way(uint64_t a, uint64_t b) {
  if (a <= b) {
    return (((a - b) > a ? 0 : (a - b)));
  } else {
    return UINT64_C(0);
  }
}

/// Unguarded: the divisor is a nonzero numeral.
uint64_t BranchFacts::half(uint64_t n) { return (n / UINT64_C(2)); }

uint64_t BranchFacts::parity(uint64_t n) { return (n % UINT64_C(2)); }

/// Guarded still: the divisor may be zero.
uint64_t BranchFacts::ratio(uint64_t x0_, uint64_t x1_) {
  return (x1_ ? x0_ / x1_ : 0);
}

uint64_t BranchFacts::rem(uint64_t x0_, uint64_t x1_) {
  return (x1_ ? x0_ % x1_ : x0_);
}

/// A match on bool returning its own truth value.
bool BranchFacts::is_small(uint64_t n) { return n < UINT64_C(10); }
