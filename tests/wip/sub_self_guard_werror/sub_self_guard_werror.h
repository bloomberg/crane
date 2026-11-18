#pragma once

#include <cstdint>

struct N {
}; /// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential

/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Subtraction of a variable from itself: the mapping guard compares the
/// variable with itself (a >= a ? a - a : 0u for N.sub a a, (a - a) > a
/// for nat), which -Wtautological-compare rejects under -Werror (the
/// comparison forms in self_comparison_werror are fixed).  Values are right.
struct SubSelfGuardWerror {
  static unsigned int f(unsigned int a);
  static uint64_t g(uint64_t a);
};
