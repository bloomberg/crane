#ifndef INCLUDED_BRANCH_PAIRS_OF_LAMBDAS
#define INCLUDED_BRANCH_PAIRS_OF_LAMBDAS

#include <cstdint>
#include <utility>

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two branches each build a pair holding a lambda: std::make_pair(0,
/// [](uint64_t x) {...})
/// deduces a distinct closure type per branch, so the conditional's operands
/// (or a lambda's two returns) have incompatible types.
struct BranchPairsOfLambdas {
  static uint64_t f(bool b);
};

#endif // INCLUDED_BRANCH_PAIRS_OF_LAMBDAS
