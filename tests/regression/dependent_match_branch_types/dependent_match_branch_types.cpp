#include "dependent_match_branch_types.h"

/// A match with a return clause computing a *different* type per branch is
/// given one C++ return type for all branches — the one the use site wants.
/// The vnil branch returns tt, whose type is unit, and clang rejects "no
/// viable conversion from returned value of type 'Unit' to function return
/// type 'Nat'".  Dependent matches whose branches agree on a type extract
/// fine.
Nat DependentMatchBranchTypes::hd(const Nat &,
                                  const DependentMatchBranchTypes::vec &v) {
  if (std::holds_alternative<typename DependentMatchBranchTypes::vec::Vnil>(
          v.v())) {
    throw std::logic_error("unreachable: impossible dependent match branch");
  } else {
    const auto &[_, a1, _] =
        std::get<typename DependentMatchBranchTypes::vec::Vcons>(v.v());
    return a1;
  }
}
