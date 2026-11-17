#include "self_comparison_werror.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Nat.leb n n (and Nat.eqb n n, Nat.ltb n n) prints n <= n; clang's
/// -Wtautological-compare rejects that under the test suite's -Werror.  The
/// value is right; the generated code does not build with Crane's own flags.
bool SelfComparisonWerror::le_self(uint64_t n) { return n <= n; }

bool SelfComparisonWerror::eq_self(uint64_t n) { return n == n; }

bool SelfComparisonWerror::lt_self(uint64_t n) { return n < n; }
