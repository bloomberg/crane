#pragma once

#include <cstdint>

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Nat.leb n n (and Nat.eqb n n, Nat.ltb n n) prints n <= n; clang's
/// -Wtautological-compare rejects that under the test suite's -Werror.  The
/// value is right; the generated code does not build with Crane's own flags.
struct SelfComparisonWerror {
  static bool le_self(uint64_t n);
  static bool eq_self(uint64_t n);
  static bool lt_self(uint64_t n);
};
