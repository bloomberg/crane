#include "bool_negation_self_werror.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// orb b (negb b) prints (b || !(b)) and andb b (negb b) prints
/// (b && !(b)); clang's -Wtautological-negation-compare rejects both under
/// the suite's -Werror.  Same family as the folded self-comparisons
/// (self_comparison_werror, self_comparison_mapped_werror).
bool BoolNegationSelfWerror::f(bool) { return true; }

bool BoolNegationSelfWerror::g(bool) { return false; }

/// The negation first.
bool BoolNegationSelfWerror::f_(bool _x) { return f(_x); }

bool BoolNegationSelfWerror::g_(bool _x) { return g(_x); }
