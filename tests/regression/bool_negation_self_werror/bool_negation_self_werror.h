#pragma once

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// orb b (negb b) prints (b || !(b)) and andb b (negb b) prints
/// (b && !(b)); clang's -Wtautological-negation-compare rejects both under
/// the suite's -Werror.  Same family as the folded self-comparisons
/// (self_comparison_werror, self_comparison_mapped_werror).
struct BoolNegationSelfWerror {
  static bool f(bool _x);
  static bool g(bool _x);
  /// The negation first.
  static bool f_(bool _x);
  static bool g_(bool _x);
};
