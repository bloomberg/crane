#include "case_of_case_result_type.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A match (or if) whose scrutinee is another match: after case-of-case the
/// immediately invoked lambda is annotated with the inner match's result type
/// instead of the outer one.
///
/// - t: inner list nat, outer nat: -> List<uint64_t> does not compile.
/// - g: inner bool, outer nat under Nat.leb: -> bool compiles and
/// turns 12 into true (1); g 3 4 is true in Rocq, false in C++.
/// - u: same at a top-level constant: Rocq 12, C++ 1.
/// - v: a projection of a match on a fold_left pair: -> pt on a lambda
/// returning px; does not compile.
/// - w: a match whose branches are all lambdas, applied to k: the
/// lambdas move out of the match and the branches kept their arrow type,
/// -> crane::fn<uint64_t(uint64_t)>; does not compile.
///
/// The wrong values have no diagnostic (with a literal left operand clang
/// flags g via -Wtautological-constant-out-of-range-compare).
uint64_t CaseOfCaseResultType::h(uint64_t n) { return (n + UINT64_C(7)); }

bool CaseOfCaseResultType::g(uint64_t k, uint64_t n) {
  return k <= [&]() -> uint64_t {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t _x = n - 1;
      return UINT64_C(12);
    }
  }();
}

/// A match applied to an argument: the argument is pushed into the
/// branches, which then return what their functions did.
bool CaseOfCaseResultType::w(uint64_t k, uint64_t n) {
  return UINT64_C(3) <= [&]() -> uint64_t {
    if (n <= 0) {
      return k;
    } else {
      uint64_t _x = n - 1;
      return (k + UINT64_C(9));
    }
  }();
}
