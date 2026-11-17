#include "branch_pairs_of_lambdas.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two branches each build a pair holding a lambda: std::make_pair(0,
/// [](uint64_t x) {...})
/// deduces a distinct closure type per branch, so the conditional's operands
/// (or a lambda's two returns) have incompatible types.
uint64_t BranchPairsOfLambdas::f(bool b) {
  return (b
              ? std::make_pair(UINT64_C(0), [](uint64_t x) { return x; })
              : std::make_pair(UINT64_C(1),
                               [](uint64_t x) {
                                 return (x + UINT64_C(1));
                               }))
             .first;
}
