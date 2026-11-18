#include "sub_self_guard_werror.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Subtraction of a variable from itself: the mapping guard compares the
/// variable with itself (a >= a ? a - a : 0u for N.sub a a, (a - a) > a
/// for nat), which -Wtautological-compare rejects under -Werror (the
/// comparison forms in self_comparison_werror are fixed).  Values are right.
unsigned int SubSelfGuardWerror::f(unsigned int) { return 0u; }

uint64_t SubSelfGuardWerror::g(uint64_t) { return UINT64_C(0); }

/// Pos.sub stops at one, so p - p is one.
unsigned int SubSelfGuardWerror::h(unsigned int) { return 1u; }
