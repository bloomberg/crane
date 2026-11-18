#include "branch_pair_fn_param_convention.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two if branches each build a pair holding a function on Rocq's string
/// (no Std mapping): one lambda reads its argument (a match), the other
/// ignores it.  After the callable-join fix both become crane::fn, but one
/// takes const String & and the other String, so the conditional is
/// ambiguous ("pair<fn<pt (const String &)>, ..> can be converted to
/// pair<fn<pt (String)>, ..> and vice versa").
uint64_t BranchPairFnParamConvention::t(bool b) {
  return (
      b
          ? std::make_pair(
                crane::fn(
                    [](const String &y) -> BranchPairFnParamConvention::pt {
                      if (std::holds_alternative<typename String::EmptyString>(
                              y.v())) {
                        return pt{UINT64_C(1), true};
                      } else {
                        return pt{UINT64_C(9), true};
                      }
                    }),
                UINT64_C(0))
          : std::make_pair(
                crane::fn([](String) { return pt{UINT64_C(2), true}; }),
                UINT64_C(0)))
             .first(String::emptystring()).px;
}
