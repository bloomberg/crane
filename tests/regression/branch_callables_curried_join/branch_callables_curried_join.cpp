#include "branch_callables_curried_join.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Match branches producing two-argument function values, one a curried
/// lambda, the other a composed let-lambda (let cf .. in let cg .. in fun c
/// => cf (cg c)), bound by a beta-redex: the C++ declares the variable at
/// one branch's type and assigns the other ("no viable overloaded '='").
/// Remaining after d7cf5aaae (common crane::fn type for joined callables).
/// A match's branches now carry the slot into their tails, so the lambda
/// knows the Core type backing the two-parameter function it is written
/// against, and takes the parameter its body leaves to a partial
/// application.
uint64_t BranchCallablesCurriedJoin::t(const List<uint64_t> &l) {
  crane::fn<bool(uint64_t, BranchCallablesCurriedJoin::pt)> w;
  auto _cs = l.length();
  if (_cs <= 0) {
    w = [](uint64_t, BranchCallablesCurriedJoin::pt) { return true; };
  } else {
    uint64_t _x = _cs - 1;
    crane::fn<bool(bool, BranchCallablesCurriedJoin::pt)> cf =
        [](bool, BranchCallablesCurriedJoin::pt) { return false; };
    crane::fn<bool(uint64_t)> cg = [](uint64_t) { return true; };
    w = [=, cf = std::move(cf), cg = std::move(cg)](
        uint64_t c,
        const BranchCallablesCurriedJoin::pt &eta0_) {
      return cf(cg(c), eta0_);
    };
  }
  if (w(UINT64_C(0), pt{UINT64_C(0), true})) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}
