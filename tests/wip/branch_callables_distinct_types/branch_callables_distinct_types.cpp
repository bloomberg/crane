#include "branch_callables_distinct_types.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two branches producing function values of different C++ types, with no
/// common type spelled for the result (the pair-of-lambdas form in
/// branch_pairs_of_lambdas is fixed):
/// - t: in a fold_left step, one branch returns a composed let-lambda,
/// the other a plain lambda: "return type '(lambda ...)' must match
/// previous return type '(lambda ...)'".
/// - u: a class method (sz) in one if branch and a lambda from a match
/// in the other, as a constructor argument: "incompatible operand types
/// ('uint64_t (uint64_t)' and '(lambda ...)')".
BranchCallablesDistinctTypes::ptree<crane::fn<uint64_t(uint64_t)>>
BranchCallablesDistinctTypes::f(bool b, List<uint64_t> l) {
  return ptree<crane::fn<uint64_t(uint64_t)>>::pnode(
      ptree<crane::fn<uint64_t(uint64_t)>>::pleaf(),
      (b ? sz_nat::sz : [=, l = std::move(l)](uint64_t) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          return UINT64_C(0);
        } else {
          return UINT64_C(4);
        }
      }),
      ptree<crane::fn<uint64_t(uint64_t)>>::pleaf());
}
